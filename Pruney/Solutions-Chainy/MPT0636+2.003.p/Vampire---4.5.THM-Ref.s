%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 192 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  327 (1015 expanded)
%              Number of equality atoms :   40 (  80 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f53,f55,f96,f108,f114])).

fof(f114,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f46,f112])).

fof(f112,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f111,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f111,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f110,f29])).

fof(f29,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f110,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f109,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(f109,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f101,f24])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f51,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f106,f49])).

fof(f49,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f106,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f105,f59])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f105,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f104,f28])).

fof(f104,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f103,f29])).

fof(f103,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f102,f23])).

fof(f102,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f100,f24])).

fof(f100,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f94,f23])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f93,f24])).

fof(f93,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f92,f54])).

fof(f54,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f92,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f86,f52])).

fof(f52,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f86,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
      | ~ r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f74,f28])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
      | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f69,f29])).

% (12252)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
      | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f36,f59])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f25,f45,f42])).

fof(f25,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f26,f48,f42])).

fof(f26,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f27,f48,f45,f42])).

fof(f27,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (12264)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (12256)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (12260)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (12251)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (12253)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (12251)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f50,f53,f55,f96,f108,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ~spl4_1 | spl4_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    $false | (~spl4_1 | spl4_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f46,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f111,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f109,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    (~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f6])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f4])).
% 0.20/0.49  fof(f4,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f101,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f51,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    spl4_1 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl4_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ~spl4_1 | spl4_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    $false | (~spl4_1 | spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f106,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl4_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl4_1),
% 0.20/0.49    inference(forward_demodulation,[],[f105,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f58,f28])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f40,f29])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(rectify,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f104,f28])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f103,f29])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f102,f23])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f100,f24])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f51,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f94,f23])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f93,f24])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f92,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f86,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f48])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 0.20/0.49    inference(resolution,[],[f75,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f42])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) | ~r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f74,f28])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X1,X2),X0) | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f69,f29])).
% 0.20/0.49  % (12252)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X1,X2),X0) | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(superposition,[],[f36,f59])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl4_1 | spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f45,f42])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl4_1 | spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f48,f42])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK2,sK0),sK1) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f48,f45,f42])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (12251)------------------------------
% 0.20/0.49  % (12251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (12251)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (12251)Memory used [KB]: 10618
% 0.20/0.49  % (12251)Time elapsed: 0.064 s
% 0.20/0.49  % (12251)------------------------------
% 0.20/0.49  % (12251)------------------------------
% 0.20/0.50  % (12243)Success in time 0.135 s
%------------------------------------------------------------------------------
