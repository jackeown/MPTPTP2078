%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 241 expanded)
%              Number of leaves         :   19 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  342 (1037 expanded)
%              Number of equality atoms :   89 ( 303 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f482,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f79,f84,f89,f94,f103,f478,f481])).

fof(f481,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f479,f83])).

fof(f83,plain,
    ( k2_funct_1(sK0) != sK1
    | spl2_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_6
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f479,plain,
    ( k2_funct_1(sK0) = sK1
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f477,f224])).

fof(f224,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f223,f133])).

fof(f133,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f68,f53,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f223,plain,
    ( k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f222,f221])).

fof(f221,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f220,f152])).

fof(f152,plain,
    ( k5_relat_1(sK1,sK0) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f151,f93])).

fof(f93,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_8
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f151,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f149,f130])).

fof(f130,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f58,f63,f78,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f78,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_5
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f63,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f149,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f58,f63,f78,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f220,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f219,f217])).

fof(f217,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f212,f118])).

fof(f118,plain,
    ( k2_relat_1(sK1) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f112,f88])).

fof(f88,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_7
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f112,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f58,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f212,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0))))
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f53,f102,f49])).

fof(f102,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_9
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f219,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f205,f139])).

fof(f139,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f138,f88])).

fof(f138,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f136,f130])).

fof(f136,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f58,f63,f78,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f205,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f102,f58,f102,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f222,plain,
    ( k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f204,f139])).

fof(f204,plain,
    ( k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f68,f58,f102,f43])).

fof(f477,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl2_15
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f478,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f130,f76,f61,f56,f475])).

fof(f103,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f95,f56,f100])).

fof(f95,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f58,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f94,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f37,f91])).

fof(f37,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    & k1_relat_1(sK0) = k2_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
        & k2_relat_1(X1) = k1_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
      & k1_relat_1(sK0) = k2_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
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
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
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
           => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
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
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f89,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:22:37 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (811335681)
% 0.15/0.37  ipcrm: permission denied for id (811368452)
% 0.15/0.39  ipcrm: permission denied for id (811466771)
% 0.21/0.40  ipcrm: permission denied for id (811565085)
% 0.21/0.40  ipcrm: permission denied for id (811597856)
% 0.21/0.41  ipcrm: permission denied for id (811630630)
% 0.21/0.41  ipcrm: permission denied for id (811663402)
% 0.21/0.42  ipcrm: permission denied for id (811696176)
% 0.21/0.42  ipcrm: permission denied for id (811728946)
% 0.21/0.43  ipcrm: permission denied for id (811761717)
% 0.21/0.43  ipcrm: permission denied for id (811827259)
% 0.21/0.44  ipcrm: permission denied for id (811860030)
% 0.21/0.45  ipcrm: permission denied for id (812056650)
% 0.21/0.46  ipcrm: permission denied for id (812154958)
% 0.21/0.46  ipcrm: permission denied for id (812187728)
% 0.21/0.47  ipcrm: permission denied for id (812220504)
% 0.21/0.47  ipcrm: permission denied for id (812253273)
% 0.21/0.48  ipcrm: permission denied for id (812449893)
% 0.21/0.49  ipcrm: permission denied for id (812482663)
% 0.21/0.49  ipcrm: permission denied for id (812580972)
% 0.21/0.49  ipcrm: permission denied for id (812613741)
% 0.21/0.50  ipcrm: permission denied for id (812646512)
% 0.21/0.51  ipcrm: permission denied for id (812777593)
% 0.21/0.51  ipcrm: permission denied for id (812843134)
% 0.37/0.62  % (15304)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.37/0.62  % (15296)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.37/0.65  % (15306)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.37/0.66  % (15299)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.37/0.66  % (15314)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.37/0.66  % (15292)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.37/0.66  % (15314)Refutation found. Thanks to Tanya!
% 0.37/0.66  % SZS status Theorem for theBenchmark
% 0.37/0.66  % SZS output start Proof for theBenchmark
% 0.37/0.66  fof(f482,plain,(
% 0.37/0.66    $false),
% 0.37/0.66    inference(avatar_sat_refutation,[],[f59,f64,f69,f79,f84,f89,f94,f103,f478,f481])).
% 0.37/0.66  fof(f481,plain,(
% 0.37/0.66    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_9 | ~spl2_15),
% 0.37/0.66    inference(avatar_contradiction_clause,[],[f480])).
% 0.37/0.66  fof(f480,plain,(
% 0.37/0.66    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_9 | ~spl2_15)),
% 0.37/0.66    inference(subsumption_resolution,[],[f479,f83])).
% 0.37/0.66  fof(f83,plain,(
% 0.37/0.66    k2_funct_1(sK0) != sK1 | spl2_6),
% 0.37/0.66    inference(avatar_component_clause,[],[f81])).
% 0.37/0.66  fof(f81,plain,(
% 0.37/0.66    spl2_6 <=> k2_funct_1(sK0) = sK1),
% 0.37/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.37/0.66  fof(f479,plain,(
% 0.37/0.66    k2_funct_1(sK0) = sK1 | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_8 | ~spl2_9 | ~spl2_15)),
% 0.37/0.66    inference(forward_demodulation,[],[f477,f224])).
% 0.37/0.66  fof(f224,plain,(
% 0.37/0.66    sK1 = k4_relat_1(sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_8 | ~spl2_9)),
% 0.37/0.66    inference(forward_demodulation,[],[f223,f133])).
% 0.37/0.66  fof(f133,plain,(
% 0.37/0.66    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_3),
% 0.37/0.66    inference(unit_resulting_resolution,[],[f68,f53,f49])).
% 0.37/0.66  fof(f49,plain,(
% 0.37/0.66    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.37/0.66    inference(cnf_transformation,[],[f25])).
% 0.37/0.66  fof(f25,plain,(
% 0.37/0.66    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.37/0.66    inference(flattening,[],[f24])).
% 0.37/0.66  fof(f24,plain,(
% 0.37/0.66    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.37/0.66    inference(ennf_transformation,[],[f6])).
% 0.37/0.66  fof(f6,axiom,(
% 0.37/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.37/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.37/0.66  fof(f53,plain,(
% 0.37/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.37/0.66    inference(equality_resolution,[],[f51])).
% 0.37/0.66  fof(f51,plain,(
% 0.37/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.37/0.66    inference(cnf_transformation,[],[f30])).
% 0.37/0.66  fof(f30,plain,(
% 0.37/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.37/0.66    inference(flattening,[],[f29])).
% 0.37/0.66  fof(f29,plain,(
% 0.37/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.37/0.66    inference(nnf_transformation,[],[f1])).
% 0.37/0.66  fof(f1,axiom,(
% 0.37/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.37/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.37/0.66  fof(f68,plain,(
% 0.37/0.66    v1_relat_1(sK1) | ~spl2_3),
% 0.37/0.66    inference(avatar_component_clause,[],[f66])).
% 0.37/0.66  fof(f66,plain,(
% 0.37/0.66    spl2_3 <=> v1_relat_1(sK1)),
% 0.37/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.37/0.66  fof(f223,plain,(
% 0.37/0.66    k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_8 | ~spl2_9)),
% 0.37/0.66    inference(forward_demodulation,[],[f222,f221])).
% 0.37/0.66  fof(f221,plain,(
% 0.37/0.66    k4_relat_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_7 | ~spl2_8 | ~spl2_9)),
% 0.37/0.66    inference(forward_demodulation,[],[f220,f152])).
% 0.37/0.66  fof(f152,plain,(
% 0.37/0.66    k5_relat_1(sK1,sK0) = k5_relat_1(k4_relat_1(sK0),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_8)),
% 0.37/0.66    inference(forward_demodulation,[],[f151,f93])).
% 0.37/0.66  fof(f93,plain,(
% 0.37/0.66    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) | ~spl2_8),
% 0.37/0.66    inference(avatar_component_clause,[],[f91])).
% 0.37/0.66  fof(f91,plain,(
% 0.37/0.66    spl2_8 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.37/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.37/0.66  fof(f151,plain,(
% 0.37/0.66    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 0.37/0.66    inference(forward_demodulation,[],[f149,f130])).
% 0.37/0.66  fof(f130,plain,(
% 0.37/0.66    k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 0.37/0.66    inference(unit_resulting_resolution,[],[f58,f63,f78,f46])).
% 0.37/0.66  fof(f46,plain,(
% 0.37/0.66    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/0.66    inference(cnf_transformation,[],[f21])).
% 0.37/0.66  fof(f21,plain,(
% 0.37/0.66    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/0.66    inference(flattening,[],[f20])).
% 0.37/0.66  fof(f20,plain,(
% 0.37/0.66    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.37/0.66    inference(ennf_transformation,[],[f7])).
% 0.37/0.66  fof(f7,axiom,(
% 0.37/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.37/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.37/0.66  fof(f78,plain,(
% 0.37/0.66    v2_funct_1(sK0) | ~spl2_5),
% 0.37/0.66    inference(avatar_component_clause,[],[f76])).
% 0.37/0.66  fof(f76,plain,(
% 0.37/0.66    spl2_5 <=> v2_funct_1(sK0)),
% 0.37/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.37/0.66  fof(f63,plain,(
% 0.37/0.66    v1_funct_1(sK0) | ~spl2_2),
% 0.37/0.66    inference(avatar_component_clause,[],[f61])).
% 0.37/0.66  fof(f61,plain,(
% 0.37/0.66    spl2_2 <=> v1_funct_1(sK0)),
% 0.37/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.37/0.66  fof(f58,plain,(
% 0.37/0.66    v1_relat_1(sK0) | ~spl2_1),
% 0.37/0.66    inference(avatar_component_clause,[],[f56])).
% 0.37/0.66  fof(f56,plain,(
% 0.37/0.66    spl2_1 <=> v1_relat_1(sK0)),
% 0.37/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.37/0.66  fof(f149,plain,(
% 0.37/0.66    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 0.37/0.66    inference(unit_resulting_resolution,[],[f58,f63,f78,f48])).
% 0.37/0.66  fof(f48,plain,(
% 0.37/0.66    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/0.66    inference(cnf_transformation,[],[f23])).
% 0.37/0.66  fof(f23,plain,(
% 0.37/0.66    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/0.66    inference(flattening,[],[f22])).
% 0.37/0.66  fof(f22,plain,(
% 0.37/0.66    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.37/0.66    inference(ennf_transformation,[],[f9])).
% 0.37/0.66  fof(f9,axiom,(
% 0.37/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.37/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.37/0.66  fof(f220,plain,(
% 0.37/0.66    k4_relat_1(sK0) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),k4_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.37/0.66    inference(forward_demodulation,[],[f219,f217])).
% 0.37/0.66  fof(f217,plain,(
% 0.37/0.66    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(sK1))) | (~spl2_1 | ~spl2_7 | ~spl2_9)),
% 0.37/0.66    inference(forward_demodulation,[],[f212,f118])).
% 0.37/0.66  fof(f118,plain,(
% 0.37/0.66    k2_relat_1(sK1) = k2_relat_1(k4_relat_1(sK0)) | (~spl2_1 | ~spl2_7)),
% 0.37/0.66    inference(forward_demodulation,[],[f112,f88])).
% 0.37/0.66  fof(f88,plain,(
% 0.37/0.66    k1_relat_1(sK0) = k2_relat_1(sK1) | ~spl2_7),
% 0.37/0.66    inference(avatar_component_clause,[],[f86])).
% 0.37/0.66  fof(f86,plain,(
% 0.37/0.66    spl2_7 <=> k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.37/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.37/0.66  fof(f112,plain,(
% 0.37/0.66    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl2_1),
% 0.37/0.66    inference(unit_resulting_resolution,[],[f58,f42])).
% 0.37/0.66  fof(f42,plain,(
% 0.37/0.66    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.37/0.66    inference(cnf_transformation,[],[f16])).
% 0.37/0.66  fof(f16,plain,(
% 0.37/0.66    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.37/0.66    inference(ennf_transformation,[],[f3])).
% 0.37/0.66  fof(f3,axiom,(
% 0.37/0.66    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.37/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.37/0.66  fof(f212,plain,(
% 0.37/0.66    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) | ~spl2_9),
% 0.37/0.66    inference(unit_resulting_resolution,[],[f53,f102,f49])).
% 0.37/0.66  fof(f102,plain,(
% 0.37/0.66    v1_relat_1(k4_relat_1(sK0)) | ~spl2_9),
% 0.37/0.66    inference(avatar_component_clause,[],[f100])).
% 0.37/0.66  fof(f100,plain,(
% 0.37/0.66    spl2_9 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.37/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.37/0.66  fof(f219,plain,(
% 0.37/0.66    k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.37/0.66    inference(forward_demodulation,[],[f205,f139])).
% 0.37/0.66  fof(f139,plain,(
% 0.37/0.66    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_7)),
% 0.37/0.66    inference(forward_demodulation,[],[f138,f88])).
% 0.37/0.66  fof(f138,plain,(
% 0.37/0.66    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 0.37/0.66    inference(forward_demodulation,[],[f136,f130])).
% 0.37/0.66  fof(f136,plain,(
% 0.37/0.66    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 0.37/0.67    inference(unit_resulting_resolution,[],[f58,f63,f78,f47])).
% 0.37/0.67  fof(f47,plain,(
% 0.37/0.67    ( ! [X0] : (~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f23])).
% 0.37/0.67  fof(f205,plain,(
% 0.37/0.67    k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl2_1 | ~spl2_9)),
% 0.37/0.67    inference(unit_resulting_resolution,[],[f102,f58,f102,f43])).
% 0.37/0.67  fof(f43,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f17])).
% 0.37/0.67  fof(f17,plain,(
% 0.37/0.67    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.37/0.67    inference(ennf_transformation,[],[f4])).
% 0.37/0.67  fof(f4,axiom,(
% 0.37/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.37/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.37/0.67  fof(f222,plain,(
% 0.37/0.67    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.37/0.67    inference(forward_demodulation,[],[f204,f139])).
% 0.37/0.67  fof(f204,plain,(
% 0.37/0.67    k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl2_1 | ~spl2_3 | ~spl2_9)),
% 0.37/0.67    inference(unit_resulting_resolution,[],[f68,f58,f102,f43])).
% 0.37/0.67  fof(f477,plain,(
% 0.37/0.67    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl2_15),
% 0.37/0.67    inference(avatar_component_clause,[],[f475])).
% 0.37/0.67  fof(f475,plain,(
% 0.37/0.67    spl2_15 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.37/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.37/0.67  fof(f478,plain,(
% 0.37/0.67    spl2_15 | ~spl2_1 | ~spl2_2 | ~spl2_5),
% 0.37/0.67    inference(avatar_split_clause,[],[f130,f76,f61,f56,f475])).
% 0.37/0.67  fof(f103,plain,(
% 0.37/0.67    spl2_9 | ~spl2_1),
% 0.37/0.67    inference(avatar_split_clause,[],[f95,f56,f100])).
% 0.37/0.67  fof(f95,plain,(
% 0.37/0.67    v1_relat_1(k4_relat_1(sK0)) | ~spl2_1),
% 0.37/0.67    inference(unit_resulting_resolution,[],[f58,f39])).
% 0.37/0.67  fof(f39,plain,(
% 0.37/0.67    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f14])).
% 0.37/0.67  fof(f14,plain,(
% 0.37/0.67    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.37/0.67    inference(ennf_transformation,[],[f2])).
% 0.37/0.67  fof(f2,axiom,(
% 0.37/0.67    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.37/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.37/0.67  fof(f94,plain,(
% 0.37/0.67    spl2_8),
% 0.37/0.67    inference(avatar_split_clause,[],[f37,f91])).
% 0.37/0.67  fof(f37,plain,(
% 0.37/0.67    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  fof(f28,plain,(
% 0.37/0.67    (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.37/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f27,f26])).
% 0.37/0.67  fof(f26,plain,(
% 0.37/0.67    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.37/0.67    introduced(choice_axiom,[])).
% 0.37/0.67  fof(f27,plain,(
% 0.37/0.67    ? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.37/0.67    introduced(choice_axiom,[])).
% 0.37/0.67  fof(f13,plain,(
% 0.37/0.67    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.37/0.67    inference(flattening,[],[f12])).
% 0.37/0.67  fof(f12,plain,(
% 0.37/0.67    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.37/0.67    inference(ennf_transformation,[],[f11])).
% 0.37/0.67  fof(f11,negated_conjecture,(
% 0.37/0.67    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.37/0.67    inference(negated_conjecture,[],[f10])).
% 0.37/0.67  fof(f10,conjecture,(
% 0.37/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.37/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.37/0.67  fof(f89,plain,(
% 0.37/0.67    spl2_7),
% 0.37/0.67    inference(avatar_split_clause,[],[f36,f86])).
% 0.37/0.67  fof(f36,plain,(
% 0.37/0.67    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  fof(f84,plain,(
% 0.37/0.67    ~spl2_6),
% 0.37/0.67    inference(avatar_split_clause,[],[f38,f81])).
% 0.37/0.67  fof(f38,plain,(
% 0.37/0.67    k2_funct_1(sK0) != sK1),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  fof(f79,plain,(
% 0.37/0.67    spl2_5),
% 0.37/0.67    inference(avatar_split_clause,[],[f35,f76])).
% 0.37/0.67  fof(f35,plain,(
% 0.37/0.67    v2_funct_1(sK0)),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  fof(f69,plain,(
% 0.37/0.67    spl2_3),
% 0.37/0.67    inference(avatar_split_clause,[],[f33,f66])).
% 0.37/0.67  fof(f33,plain,(
% 0.37/0.67    v1_relat_1(sK1)),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  fof(f64,plain,(
% 0.37/0.67    spl2_2),
% 0.37/0.67    inference(avatar_split_clause,[],[f32,f61])).
% 0.37/0.67  fof(f32,plain,(
% 0.37/0.67    v1_funct_1(sK0)),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  fof(f59,plain,(
% 0.37/0.67    spl2_1),
% 0.37/0.67    inference(avatar_split_clause,[],[f31,f56])).
% 0.37/0.67  fof(f31,plain,(
% 0.37/0.67    v1_relat_1(sK0)),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  % SZS output end Proof for theBenchmark
% 0.37/0.67  % (15314)------------------------------
% 0.37/0.67  % (15314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (15314)Termination reason: Refutation
% 0.37/0.67  
% 0.37/0.67  % (15314)Memory used [KB]: 10874
% 0.37/0.67  % (15314)Time elapsed: 0.102 s
% 0.37/0.67  % (15314)------------------------------
% 0.37/0.67  % (15314)------------------------------
% 0.37/0.67  % (15295)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.37/0.67  % (15293)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.37/0.67  % (15291)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.37/0.67  % (15307)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.37/0.67  % (15312)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.37/0.68  % (15294)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.37/0.68  % (15308)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.37/0.68  % (15310)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.37/0.68  % (15300)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.37/0.68  % (15297)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.37/0.69  % (15156)Success in time 0.326 s
%------------------------------------------------------------------------------
