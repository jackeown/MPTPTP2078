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
% DateTime   : Thu Dec  3 12:52:53 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 244 expanded)
%              Number of leaves         :   14 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  305 (1054 expanded)
%              Number of equality atoms :   68 ( 349 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f83,f88,f91,f112,f164])).

fof(f164,plain,
    ( spl1_2
    | ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f162,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

% (5973)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f22,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (5970)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f162,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f161,f26])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f161,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f160,f27])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f160,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f156,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f156,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f154,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f154,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f153,f25])).

fof(f153,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f149,f67])).

fof(f67,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f149,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(superposition,[],[f48,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f48,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f112,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl1_6 ),
    inference(subsumption_resolution,[],[f110,f25])).

fof(f110,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f109,f26])).

fof(f109,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f108,f27])).

fof(f108,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(trivial_inequality_removal,[],[f107])).

fof(f107,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(superposition,[],[f106,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f34,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f106,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | spl1_6 ),
    inference(subsumption_resolution,[],[f105,f25])).

fof(f105,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f104,f26])).

fof(f104,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f102,f27])).

fof(f102,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(superposition,[],[f82,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k10_relat_1(k4_relat_1(X0),k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k10_relat_1(k4_relat_1(X0),k1_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f30,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f33])).

fof(f30,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f82,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl1_6
  <=> k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f91,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl1_5 ),
    inference(subsumption_resolution,[],[f89,f25])).

fof(f89,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(resolution,[],[f78,f29])).

fof(f78,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl1_5
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f88,plain,
    ( ~ spl1_5
    | spl1_3 ),
    inference(avatar_split_clause,[],[f87,f66,f76])).

fof(f87,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_3 ),
    inference(subsumption_resolution,[],[f86,f25])).

fof(f86,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f85,f26])).

fof(f85,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f84,f27])).

fof(f84,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(superposition,[],[f68,f33])).

fof(f68,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f83,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_1 ),
    inference(avatar_split_clause,[],[f74,f42,f80,f76])).

fof(f42,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f74,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f63,f25])).

fof(f63,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_1 ),
    inference(superposition,[],[f54,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f54,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f53,f25])).

fof(f53,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(subsumption_resolution,[],[f52,f26])).

fof(f52,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f44,f33])).

fof(f44,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f49,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f28,f46,f42])).

fof(f28,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.58  % (5975)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.58  % (5954)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.58  % (5958)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.57/0.58  % (5957)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.57/0.58  % (5962)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.57/0.58  % (5967)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.57/0.58  % (5964)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.57/0.58  % (5959)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.57/0.58  % (5966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.57/0.59  % (5956)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.57/0.59  % (5956)Refutation found. Thanks to Tanya!
% 1.57/0.59  % SZS status Theorem for theBenchmark
% 1.57/0.59  % SZS output start Proof for theBenchmark
% 1.57/0.59  fof(f165,plain,(
% 1.57/0.59    $false),
% 1.57/0.59    inference(avatar_sat_refutation,[],[f49,f83,f88,f91,f112,f164])).
% 1.57/0.59  fof(f164,plain,(
% 1.57/0.59    spl1_2 | ~spl1_3),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f163])).
% 1.57/0.59  fof(f163,plain,(
% 1.57/0.59    $false | (spl1_2 | ~spl1_3)),
% 1.57/0.59    inference(subsumption_resolution,[],[f162,f25])).
% 1.57/0.59  fof(f25,plain,(
% 1.57/0.59    v1_relat_1(sK0)),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  % (5973)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.57/0.59  fof(f22,plain,(
% 1.57/0.59    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f21])).
% 1.57/0.59  fof(f21,plain,(
% 1.57/0.59    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f11,plain,(
% 1.57/0.59    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f10])).
% 1.57/0.59  fof(f10,plain,(
% 1.57/0.59    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f9])).
% 1.57/0.59  % (5970)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.57/0.59  fof(f9,negated_conjecture,(
% 1.57/0.59    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.57/0.59    inference(negated_conjecture,[],[f8])).
% 1.57/0.59  fof(f8,conjecture,(
% 1.57/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 1.57/0.59  fof(f162,plain,(
% 1.57/0.59    ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 1.57/0.59    inference(subsumption_resolution,[],[f161,f26])).
% 1.57/0.59  fof(f26,plain,(
% 1.57/0.59    v1_funct_1(sK0)),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f161,plain,(
% 1.57/0.59    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 1.57/0.59    inference(subsumption_resolution,[],[f160,f27])).
% 1.57/0.59  fof(f27,plain,(
% 1.57/0.59    v2_funct_1(sK0)),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f160,plain,(
% 1.57/0.59    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 1.57/0.59    inference(subsumption_resolution,[],[f156,f39])).
% 1.57/0.59  fof(f39,plain,(
% 1.57/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.59    inference(equality_resolution,[],[f37])).
% 1.57/0.59  fof(f37,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.57/0.59    inference(cnf_transformation,[],[f24])).
% 1.57/0.59  fof(f24,plain,(
% 1.57/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.59    inference(flattening,[],[f23])).
% 1.57/0.59  fof(f23,plain,(
% 1.57/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.59    inference(nnf_transformation,[],[f1])).
% 1.57/0.59  fof(f1,axiom,(
% 1.57/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.59  fof(f156,plain,(
% 1.57/0.59    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 1.57/0.59    inference(superposition,[],[f154,f35])).
% 1.57/0.59  fof(f35,plain,(
% 1.57/0.59    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f20])).
% 1.57/0.59  fof(f20,plain,(
% 1.57/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f19])).
% 1.57/0.59  fof(f19,plain,(
% 1.57/0.59    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f7])).
% 1.57/0.59  fof(f7,axiom,(
% 1.57/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.57/0.59  fof(f154,plain,(
% 1.57/0.59    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | (spl1_2 | ~spl1_3)),
% 1.57/0.59    inference(subsumption_resolution,[],[f153,f25])).
% 1.57/0.59  fof(f153,plain,(
% 1.57/0.59    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 1.57/0.59    inference(subsumption_resolution,[],[f149,f67])).
% 1.57/0.59  fof(f67,plain,(
% 1.57/0.59    v1_relat_1(k2_funct_1(sK0)) | ~spl1_3),
% 1.57/0.59    inference(avatar_component_clause,[],[f66])).
% 1.57/0.59  fof(f66,plain,(
% 1.57/0.59    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.57/0.59  fof(f149,plain,(
% 1.57/0.59    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_2),
% 1.57/0.59    inference(trivial_inequality_removal,[],[f148])).
% 1.57/0.59  fof(f148,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k2_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_2),
% 1.57/0.59    inference(superposition,[],[f48,f32])).
% 1.57/0.59  fof(f32,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f16])).
% 1.57/0.59  fof(f16,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f15])).
% 1.57/0.59  fof(f15,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f5])).
% 1.57/0.59  fof(f5,axiom,(
% 1.57/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 1.57/0.59  fof(f48,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 1.57/0.59    inference(avatar_component_clause,[],[f46])).
% 1.57/0.59  fof(f46,plain,(
% 1.57/0.59    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.57/0.59  fof(f112,plain,(
% 1.57/0.59    spl1_6),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f111])).
% 1.57/0.59  fof(f111,plain,(
% 1.57/0.59    $false | spl1_6),
% 1.57/0.59    inference(subsumption_resolution,[],[f110,f25])).
% 1.57/0.59  fof(f110,plain,(
% 1.57/0.59    ~v1_relat_1(sK0) | spl1_6),
% 1.57/0.59    inference(subsumption_resolution,[],[f109,f26])).
% 1.57/0.59  fof(f109,plain,(
% 1.57/0.59    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 1.57/0.59    inference(subsumption_resolution,[],[f108,f27])).
% 1.57/0.59  fof(f108,plain,(
% 1.57/0.59    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 1.57/0.59    inference(trivial_inequality_removal,[],[f107])).
% 1.57/0.59  fof(f107,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 1.57/0.59    inference(superposition,[],[f106,f56])).
% 1.57/0.59  fof(f56,plain,(
% 1.57/0.59    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f55])).
% 1.57/0.59  fof(f55,plain,(
% 1.57/0.59    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(superposition,[],[f34,f33])).
% 1.57/0.59  fof(f33,plain,(
% 1.57/0.59    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f18])).
% 1.57/0.59  fof(f18,plain,(
% 1.57/0.59    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f17])).
% 1.57/0.59  fof(f17,plain,(
% 1.57/0.59    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f6])).
% 1.57/0.59  fof(f6,axiom,(
% 1.57/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.57/0.59  fof(f34,plain,(
% 1.57/0.59    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f20])).
% 1.57/0.59  fof(f106,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | spl1_6),
% 1.57/0.59    inference(subsumption_resolution,[],[f105,f25])).
% 1.57/0.59  fof(f105,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_6),
% 1.57/0.59    inference(subsumption_resolution,[],[f104,f26])).
% 1.57/0.59  fof(f104,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 1.57/0.59    inference(subsumption_resolution,[],[f102,f27])).
% 1.57/0.59  fof(f102,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 1.57/0.59    inference(superposition,[],[f82,f61])).
% 1.57/0.59  fof(f61,plain,(
% 1.57/0.59    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k10_relat_1(k4_relat_1(X0),k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(subsumption_resolution,[],[f60,f29])).
% 1.57/0.59  fof(f29,plain,(
% 1.57/0.59    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f12])).
% 1.57/0.59  fof(f12,plain,(
% 1.57/0.59    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f2])).
% 1.57/0.59  fof(f2,axiom,(
% 1.57/0.59    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.57/0.59  fof(f60,plain,(
% 1.57/0.59    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k10_relat_1(k4_relat_1(X0),k1_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(superposition,[],[f30,f59])).
% 1.57/0.59  fof(f59,plain,(
% 1.57/0.59    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f57])).
% 1.57/0.59  fof(f57,plain,(
% 1.57/0.59    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(superposition,[],[f35,f33])).
% 1.57/0.59  fof(f30,plain,(
% 1.57/0.59    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f13])).
% 1.57/0.59  fof(f13,plain,(
% 1.57/0.59    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f3])).
% 1.57/0.59  fof(f3,axiom,(
% 1.57/0.59    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.57/0.59  fof(f82,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) | spl1_6),
% 1.57/0.59    inference(avatar_component_clause,[],[f80])).
% 1.57/0.59  fof(f80,plain,(
% 1.57/0.59    spl1_6 <=> k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.57/0.59  fof(f91,plain,(
% 1.57/0.59    spl1_5),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f90])).
% 1.57/0.59  fof(f90,plain,(
% 1.57/0.59    $false | spl1_5),
% 1.57/0.59    inference(subsumption_resolution,[],[f89,f25])).
% 1.57/0.59  fof(f89,plain,(
% 1.57/0.59    ~v1_relat_1(sK0) | spl1_5),
% 1.57/0.59    inference(resolution,[],[f78,f29])).
% 1.57/0.59  fof(f78,plain,(
% 1.57/0.59    ~v1_relat_1(k4_relat_1(sK0)) | spl1_5),
% 1.57/0.59    inference(avatar_component_clause,[],[f76])).
% 1.57/0.59  fof(f76,plain,(
% 1.57/0.59    spl1_5 <=> v1_relat_1(k4_relat_1(sK0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.57/0.59  fof(f88,plain,(
% 1.57/0.59    ~spl1_5 | spl1_3),
% 1.57/0.59    inference(avatar_split_clause,[],[f87,f66,f76])).
% 1.57/0.59  fof(f87,plain,(
% 1.57/0.59    ~v1_relat_1(k4_relat_1(sK0)) | spl1_3),
% 1.57/0.59    inference(subsumption_resolution,[],[f86,f25])).
% 1.57/0.59  fof(f86,plain,(
% 1.57/0.59    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_3),
% 1.57/0.59    inference(subsumption_resolution,[],[f85,f26])).
% 1.57/0.59  fof(f85,plain,(
% 1.57/0.59    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 1.57/0.59    inference(subsumption_resolution,[],[f84,f27])).
% 1.57/0.59  fof(f84,plain,(
% 1.57/0.59    ~v1_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 1.57/0.59    inference(superposition,[],[f68,f33])).
% 1.57/0.59  fof(f68,plain,(
% 1.57/0.59    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 1.57/0.59    inference(avatar_component_clause,[],[f66])).
% 1.57/0.59  fof(f83,plain,(
% 1.57/0.59    ~spl1_5 | ~spl1_6 | spl1_1),
% 1.57/0.59    inference(avatar_split_clause,[],[f74,f42,f80,f76])).
% 1.57/0.59  fof(f42,plain,(
% 1.57/0.59    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.57/0.59  fof(f74,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_1),
% 1.57/0.59    inference(subsumption_resolution,[],[f63,f25])).
% 1.57/0.59  fof(f63,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_1),
% 1.57/0.59    inference(superposition,[],[f54,f31])).
% 1.57/0.59  fof(f31,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f14])).
% 1.57/0.59  fof(f14,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f4])).
% 1.57/0.59  fof(f4,axiom,(
% 1.57/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.57/0.59  fof(f54,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | spl1_1),
% 1.57/0.59    inference(subsumption_resolution,[],[f53,f25])).
% 1.57/0.59  fof(f53,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~v1_relat_1(sK0) | spl1_1),
% 1.57/0.59    inference(subsumption_resolution,[],[f52,f26])).
% 1.57/0.59  fof(f52,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_1),
% 1.57/0.59    inference(subsumption_resolution,[],[f51,f27])).
% 1.57/0.59  fof(f51,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_1),
% 1.57/0.59    inference(superposition,[],[f44,f33])).
% 1.57/0.59  fof(f44,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 1.57/0.59    inference(avatar_component_clause,[],[f42])).
% 1.57/0.59  fof(f49,plain,(
% 1.57/0.59    ~spl1_1 | ~spl1_2),
% 1.57/0.59    inference(avatar_split_clause,[],[f28,f46,f42])).
% 1.57/0.59  fof(f28,plain,(
% 1.57/0.59    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  % SZS output end Proof for theBenchmark
% 1.57/0.59  % (5956)------------------------------
% 1.57/0.59  % (5956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (5956)Termination reason: Refutation
% 1.57/0.59  
% 1.57/0.60  % (5956)Memory used [KB]: 6140
% 1.57/0.60  % (5956)Time elapsed: 0.142 s
% 1.57/0.60  % (5956)------------------------------
% 1.57/0.60  % (5956)------------------------------
% 1.57/0.60  % (5965)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.76/0.60  % (5951)Success in time 0.226 s
%------------------------------------------------------------------------------
