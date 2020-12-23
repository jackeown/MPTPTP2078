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
% DateTime   : Thu Dec  3 12:52:44 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 153 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  370 ( 893 expanded)
%              Number of equality atoms :  111 ( 269 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f84,f115,f122,f132])).

fof(f132,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f130,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
      | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
          | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
        & r2_hidden(X0,k1_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
        | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f130,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f129,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_4 ),
    inference(resolution,[],[f114,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f114,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_4
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f122,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f120,f21])).

fof(f120,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f119,f22])).

fof(f119,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(resolution,[],[f111,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f111,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_3
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f115,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f108,f56,f53,f113,f110])).

fof(f53,plain,
    ( spl4_1
  <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f56,plain,
    ( spl4_2
  <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f107,f21])).

fof(f107,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f106,f22])).

fof(f106,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f102,f24])).

fof(f24,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_2 ),
    inference(superposition,[],[f57,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
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
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f57,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f84,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f82,f21])).

fof(f82,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f81,f22])).

fof(f81,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f80,f23])).

fof(f23,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f77,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(superposition,[],[f54,f60])).

fof(f60,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f59,f26])).

fof(f59,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f44,f27])).

fof(f44,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X1,X4) = X5
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
                  | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
                & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
              | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
                  | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
          & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
          & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
        | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
            | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
          & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f54,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f58,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f56,f53])).

fof(f25,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:39:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (812875776)
% 0.14/0.38  ipcrm: permission denied for id (813137930)
% 0.14/0.38  ipcrm: permission denied for id (813203468)
% 0.14/0.39  ipcrm: permission denied for id (813269006)
% 0.14/0.39  ipcrm: permission denied for id (813334544)
% 0.22/0.39  ipcrm: permission denied for id (813367313)
% 0.22/0.39  ipcrm: permission denied for id (813432852)
% 0.22/0.40  ipcrm: permission denied for id (813563928)
% 0.22/0.40  ipcrm: permission denied for id (813596697)
% 0.22/0.40  ipcrm: permission denied for id (813629466)
% 0.22/0.40  ipcrm: permission denied for id (813662235)
% 0.22/0.41  ipcrm: permission denied for id (813727774)
% 0.22/0.41  ipcrm: permission denied for id (813760543)
% 0.22/0.41  ipcrm: permission denied for id (813793313)
% 0.22/0.42  ipcrm: permission denied for id (814022697)
% 0.22/0.43  ipcrm: permission denied for id (814153774)
% 0.22/0.43  ipcrm: permission denied for id (814186543)
% 0.22/0.43  ipcrm: permission denied for id (814219313)
% 0.22/0.43  ipcrm: permission denied for id (814252083)
% 0.22/0.44  ipcrm: permission denied for id (814383159)
% 0.22/0.44  ipcrm: permission denied for id (814448697)
% 0.22/0.44  ipcrm: permission denied for id (814514236)
% 0.22/0.45  ipcrm: permission denied for id (814612544)
% 0.22/0.45  ipcrm: permission denied for id (814710851)
% 0.22/0.45  ipcrm: permission denied for id (814776389)
% 0.22/0.45  ipcrm: permission denied for id (814809158)
% 0.22/0.46  ipcrm: permission denied for id (814940235)
% 0.22/0.46  ipcrm: permission denied for id (814973004)
% 0.22/0.46  ipcrm: permission denied for id (815005773)
% 0.22/0.47  ipcrm: permission denied for id (815104082)
% 0.22/0.47  ipcrm: permission denied for id (815169619)
% 0.22/0.47  ipcrm: permission denied for id (815267926)
% 0.22/0.48  ipcrm: permission denied for id (815399004)
% 0.22/0.48  ipcrm: permission denied for id (815464542)
% 0.22/0.49  ipcrm: permission denied for id (815497311)
% 0.22/0.49  ipcrm: permission denied for id (815628386)
% 0.22/0.49  ipcrm: permission denied for id (815693924)
% 0.22/0.49  ipcrm: permission denied for id (815726694)
% 0.22/0.50  ipcrm: permission denied for id (815759464)
% 0.22/0.50  ipcrm: permission denied for id (815825002)
% 0.22/0.50  ipcrm: permission denied for id (815857771)
% 0.22/0.50  ipcrm: permission denied for id (815890542)
% 0.22/0.51  ipcrm: permission denied for id (816021619)
% 0.22/0.51  ipcrm: permission denied for id (816054388)
% 0.22/0.51  ipcrm: permission denied for id (816119926)
% 0.36/0.52  ipcrm: permission denied for id (816218234)
% 0.36/0.53  ipcrm: permission denied for id (816382079)
% 0.39/0.60  % (11422)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.39/0.61  % (11422)Refutation found. Thanks to Tanya!
% 0.39/0.61  % SZS status Theorem for theBenchmark
% 0.39/0.61  % SZS output start Proof for theBenchmark
% 0.39/0.61  fof(f133,plain,(
% 0.39/0.61    $false),
% 0.39/0.61    inference(avatar_sat_refutation,[],[f58,f84,f115,f122,f132])).
% 0.39/0.61  fof(f132,plain,(
% 0.39/0.61    spl4_4),
% 0.39/0.61    inference(avatar_contradiction_clause,[],[f131])).
% 0.39/0.61  fof(f131,plain,(
% 0.39/0.61    $false | spl4_4),
% 0.39/0.61    inference(subsumption_resolution,[],[f130,f21])).
% 0.39/0.61  fof(f21,plain,(
% 0.39/0.61    v1_relat_1(sK1)),
% 0.39/0.61    inference(cnf_transformation,[],[f15])).
% 0.39/0.61  fof(f15,plain,(
% 0.39/0.61    (sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.39/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14])).
% 0.39/0.61  fof(f14,plain,(
% 0.39/0.61    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.39/0.61    introduced(choice_axiom,[])).
% 0.39/0.61  fof(f7,plain,(
% 0.39/0.61    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.39/0.61    inference(flattening,[],[f6])).
% 0.39/0.61  fof(f6,plain,(
% 0.39/0.61    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.39/0.61    inference(ennf_transformation,[],[f5])).
% 0.39/0.61  fof(f5,negated_conjecture,(
% 0.39/0.61    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.39/0.61    inference(negated_conjecture,[],[f4])).
% 0.39/0.61  fof(f4,conjecture,(
% 0.39/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.39/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.39/0.61  fof(f130,plain,(
% 0.39/0.61    ~v1_relat_1(sK1) | spl4_4),
% 0.39/0.61    inference(subsumption_resolution,[],[f129,f22])).
% 0.39/0.61  fof(f22,plain,(
% 0.39/0.61    v1_funct_1(sK1)),
% 0.39/0.61    inference(cnf_transformation,[],[f15])).
% 0.39/0.61  fof(f129,plain,(
% 0.39/0.61    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_4),
% 0.39/0.61    inference(resolution,[],[f114,f27])).
% 0.39/0.61  fof(f27,plain,(
% 0.39/0.61    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.39/0.61    inference(cnf_transformation,[],[f9])).
% 0.39/0.61  fof(f9,plain,(
% 0.39/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.39/0.61    inference(flattening,[],[f8])).
% 0.39/0.61  fof(f8,plain,(
% 0.39/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.39/0.61    inference(ennf_transformation,[],[f1])).
% 0.39/0.61  fof(f1,axiom,(
% 0.39/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.39/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.39/0.61  fof(f114,plain,(
% 0.39/0.61    ~v1_funct_1(k2_funct_1(sK1)) | spl4_4),
% 0.39/0.61    inference(avatar_component_clause,[],[f113])).
% 0.39/0.61  fof(f113,plain,(
% 0.39/0.61    spl4_4 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.39/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.39/0.61  fof(f122,plain,(
% 0.39/0.61    spl4_3),
% 0.39/0.61    inference(avatar_contradiction_clause,[],[f121])).
% 0.39/0.61  fof(f121,plain,(
% 0.39/0.61    $false | spl4_3),
% 0.39/0.61    inference(subsumption_resolution,[],[f120,f21])).
% 0.39/0.61  fof(f120,plain,(
% 0.39/0.61    ~v1_relat_1(sK1) | spl4_3),
% 0.39/0.61    inference(subsumption_resolution,[],[f119,f22])).
% 0.39/0.61  fof(f119,plain,(
% 0.39/0.61    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_3),
% 0.39/0.61    inference(resolution,[],[f111,f26])).
% 0.39/0.61  fof(f26,plain,(
% 0.39/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.39/0.61    inference(cnf_transformation,[],[f9])).
% 0.39/0.61  fof(f111,plain,(
% 0.39/0.61    ~v1_relat_1(k2_funct_1(sK1)) | spl4_3),
% 0.39/0.61    inference(avatar_component_clause,[],[f110])).
% 0.39/0.61  fof(f110,plain,(
% 0.39/0.61    spl4_3 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.39/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.39/0.61  fof(f115,plain,(
% 0.39/0.61    ~spl4_3 | ~spl4_4 | ~spl4_1 | spl4_2),
% 0.39/0.61    inference(avatar_split_clause,[],[f108,f56,f53,f113,f110])).
% 0.39/0.61  fof(f53,plain,(
% 0.39/0.61    spl4_1 <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.39/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.39/0.61  fof(f56,plain,(
% 0.39/0.61    spl4_2 <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.39/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.39/0.61  fof(f108,plain,(
% 0.39/0.61    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.39/0.61    inference(subsumption_resolution,[],[f107,f21])).
% 0.39/0.61  fof(f107,plain,(
% 0.39/0.61    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | spl4_2),
% 0.39/0.61    inference(subsumption_resolution,[],[f106,f22])).
% 0.39/0.61  fof(f106,plain,(
% 0.39/0.61    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_2),
% 0.39/0.61    inference(subsumption_resolution,[],[f102,f24])).
% 0.39/0.61  fof(f24,plain,(
% 0.39/0.61    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.39/0.61    inference(cnf_transformation,[],[f15])).
% 0.39/0.61  fof(f102,plain,(
% 0.39/0.61    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_2),
% 0.39/0.61    inference(superposition,[],[f57,f42])).
% 0.39/0.61  fof(f42,plain,(
% 0.39/0.61    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.39/0.61    inference(cnf_transformation,[],[f13])).
% 0.39/0.61  fof(f13,plain,(
% 0.39/0.61    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.39/0.61    inference(flattening,[],[f12])).
% 0.39/0.61  fof(f12,plain,(
% 0.39/0.61    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.39/0.61    inference(ennf_transformation,[],[f2])).
% 0.39/0.61  fof(f2,axiom,(
% 0.39/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.39/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.39/0.61  fof(f57,plain,(
% 0.39/0.61    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | spl4_2),
% 0.39/0.61    inference(avatar_component_clause,[],[f56])).
% 0.39/0.61  fof(f84,plain,(
% 0.39/0.61    spl4_1),
% 0.39/0.61    inference(avatar_contradiction_clause,[],[f83])).
% 0.39/0.61  fof(f83,plain,(
% 0.39/0.61    $false | spl4_1),
% 0.39/0.61    inference(subsumption_resolution,[],[f82,f21])).
% 0.39/0.61  fof(f82,plain,(
% 0.39/0.61    ~v1_relat_1(sK1) | spl4_1),
% 0.39/0.61    inference(subsumption_resolution,[],[f81,f22])).
% 0.39/0.61  fof(f81,plain,(
% 0.39/0.61    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.39/0.61    inference(subsumption_resolution,[],[f80,f23])).
% 0.39/0.61  fof(f23,plain,(
% 0.39/0.61    v2_funct_1(sK1)),
% 0.39/0.61    inference(cnf_transformation,[],[f15])).
% 0.39/0.61  fof(f80,plain,(
% 0.39/0.61    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.39/0.61    inference(subsumption_resolution,[],[f77,f24])).
% 0.39/0.61  fof(f77,plain,(
% 0.39/0.61    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.39/0.61    inference(trivial_inequality_removal,[],[f73])).
% 0.39/0.61  fof(f73,plain,(
% 0.39/0.61    sK0 != sK0 | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.39/0.61    inference(superposition,[],[f54,f60])).
% 0.39/0.61  fof(f60,plain,(
% 0.39/0.61    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.39/0.61    inference(subsumption_resolution,[],[f59,f26])).
% 0.39/0.61  fof(f59,plain,(
% 0.39/0.61    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.39/0.61    inference(subsumption_resolution,[],[f44,f27])).
% 0.39/0.61  fof(f44,plain,(
% 0.39/0.61    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.39/0.61    inference(equality_resolution,[],[f43])).
% 0.39/0.61  fof(f43,plain,(
% 0.39/0.61    ( ! [X0,X5,X1] : (k1_funct_1(X1,k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.39/0.61    inference(equality_resolution,[],[f32])).
% 0.39/0.61  fof(f32,plain,(
% 0.39/0.61    ( ! [X4,X0,X5,X1] : (k1_funct_1(X1,X4) = X5 | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.39/0.61    inference(cnf_transformation,[],[f20])).
% 0.39/0.61  fof(f20,plain,(
% 0.39/0.61    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.39/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).
% 0.39/0.61  fof(f19,plain,(
% 0.39/0.61    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) => (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))))),
% 0.39/0.61    introduced(choice_axiom,[])).
% 0.39/0.61  fof(f18,plain,(
% 0.39/0.61    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.39/0.61    inference(rectify,[],[f17])).
% 0.39/0.61  fof(f17,plain,(
% 0.39/0.61    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.39/0.61    inference(flattening,[],[f16])).
% 0.39/0.61  fof(f16,plain,(
% 0.39/0.61    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.39/0.61    inference(nnf_transformation,[],[f11])).
% 0.39/0.61  fof(f11,plain,(
% 0.39/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.39/0.61    inference(flattening,[],[f10])).
% 0.39/0.61  fof(f10,plain,(
% 0.39/0.61    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.39/0.61    inference(ennf_transformation,[],[f3])).
% 0.39/0.61  fof(f3,axiom,(
% 0.39/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.39/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.39/0.61  fof(f54,plain,(
% 0.39/0.61    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | spl4_1),
% 0.39/0.61    inference(avatar_component_clause,[],[f53])).
% 0.39/0.61  fof(f58,plain,(
% 0.39/0.61    ~spl4_1 | ~spl4_2),
% 0.39/0.61    inference(avatar_split_clause,[],[f25,f56,f53])).
% 0.39/0.61  fof(f25,plain,(
% 0.39/0.61    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.39/0.61    inference(cnf_transformation,[],[f15])).
% 0.39/0.61  % SZS output end Proof for theBenchmark
% 0.39/0.61  % (11422)------------------------------
% 0.39/0.61  % (11422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.61  % (11422)Termination reason: Refutation
% 0.39/0.61  
% 0.39/0.61  % (11422)Memory used [KB]: 10618
% 0.39/0.61  % (11422)Time elapsed: 0.043 s
% 0.39/0.61  % (11422)------------------------------
% 0.39/0.61  % (11422)------------------------------
% 0.39/0.61  % (11277)Success in time 0.248 s
%------------------------------------------------------------------------------
