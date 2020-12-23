%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0701+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 330 expanded)
%              Number of leaves         :   15 ( 125 expanded)
%              Depth                    :   35
%              Number of atoms          :  459 (3297 expanded)
%              Number of equality atoms :  140 (1547 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f457])).

fof(f457,plain,(
    ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f455,f35])).

fof(f35,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK5 != sK6
    & k5_relat_1(sK4,sK5) = k5_relat_1(sK4,sK6)
    & sK3 = k1_relat_1(sK6)
    & sK3 = k1_relat_1(sK5)
    & sK3 = k2_relat_1(sK4)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f7,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                & k1_relat_1(X3) = X0
                & k1_relat_1(X2) = X0
                & k2_relat_1(X1) = X0
                & v1_funct_1(X3)
                & v1_relat_1(X3) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(sK4,X2) = k5_relat_1(sK4,X3)
              & k1_relat_1(X3) = sK3
              & k1_relat_1(X2) = sK3
              & sK3 = k2_relat_1(sK4)
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( X2 != X3
            & k5_relat_1(sK4,X2) = k5_relat_1(sK4,X3)
            & k1_relat_1(X3) = sK3
            & k1_relat_1(X2) = sK3
            & sK3 = k2_relat_1(sK4)
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( sK5 != X3
          & k5_relat_1(sK4,X3) = k5_relat_1(sK4,sK5)
          & k1_relat_1(X3) = sK3
          & sK3 = k1_relat_1(sK5)
          & sK3 = k2_relat_1(sK4)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( sK5 != X3
        & k5_relat_1(sK4,X3) = k5_relat_1(sK4,sK5)
        & k1_relat_1(X3) = sK3
        & sK3 = k1_relat_1(sK5)
        & sK3 = k2_relat_1(sK4)
        & v1_funct_1(X3)
        & v1_relat_1(X3) )
   => ( sK5 != sK6
      & k5_relat_1(sK4,sK5) = k5_relat_1(sK4,sK6)
      & sK3 = k1_relat_1(sK6)
      & sK3 = k1_relat_1(sK5)
      & sK3 = k2_relat_1(sK4)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_relat_1(X3) )
               => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                    & k1_relat_1(X3) = X0
                    & k1_relat_1(X2) = X0
                    & k2_relat_1(X1) = X0 )
                 => X2 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

fof(f455,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f454,f36])).

fof(f36,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f454,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f453,f40])).

fof(f40,plain,(
    sK3 = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f453,plain,
    ( sK3 != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f452,f43])).

fof(f43,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f21])).

fof(f452,plain,
    ( sK5 = sK6
    | sK3 != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl10_2 ),
    inference(resolution,[],[f451,f116])).

fof(f116,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK6,X1),sK3)
      | sK6 = X1
      | k1_relat_1(X1) != sK3
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f115,f37])).

fof(f37,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f115,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK6,X1),sK3)
      | sK6 = X1
      | k1_relat_1(X1) != sK3
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f112,f38])).

fof(f38,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f112,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK6,X1),sK3)
      | sK6 = X1
      | k1_relat_1(X1) != sK3
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(superposition,[],[f44,f41])).

fof(f41,plain,(
    sK3 = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f9,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f451,plain,
    ( ~ r2_hidden(sK7(sK6,sK5),sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f450,f84])).

fof(f84,plain,
    ( ! [X2] :
        ( sP0(X2,sK4)
        | ~ r2_hidden(X2,sK3) )
    | ~ spl10_2 ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,
    ( sP1(sK4,sK3)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl10_2
  <=> sP1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK8(X0,X1),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sP0(sK8(X0,X1),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK8(X0,X1),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sP0(sK8(X0,X1),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f450,plain,(
    ~ sP0(sK7(sK6,sK5),sK4) ),
    inference(subsumption_resolution,[],[f449,f35])).

fof(f449,plain,
    ( ~ v1_relat_1(sK5)
    | ~ sP0(sK7(sK6,sK5),sK4) ),
    inference(subsumption_resolution,[],[f448,f36])).

fof(f448,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ sP0(sK7(sK6,sK5),sK4) ),
    inference(subsumption_resolution,[],[f447,f43])).

fof(f447,plain,
    ( sK5 = sK6
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ sP0(sK7(sK6,sK5),sK4) ),
    inference(subsumption_resolution,[],[f446,f40])).

fof(f446,plain,
    ( sK3 != k1_relat_1(sK5)
    | sK5 = sK6
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ sP0(sK7(sK6,sK5),sK4) ),
    inference(equality_resolution,[],[f172])).

fof(f172,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,sK7(sK6,X4)) != k1_funct_1(X4,sK7(sK6,X4))
      | sK3 != k1_relat_1(X4)
      | sK6 = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ sP0(sK7(sK6,X4),sK4) ) ),
    inference(forward_demodulation,[],[f171,f41])).

fof(f171,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,sK7(sK6,X4)) != k1_funct_1(X4,sK7(sK6,X4))
      | sK6 = X4
      | k1_relat_1(sK6) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ sP0(sK7(sK6,X4),sK4) ) ),
    inference(subsumption_resolution,[],[f170,f37])).

fof(f170,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,sK7(sK6,X4)) != k1_funct_1(X4,sK7(sK6,X4))
      | sK6 = X4
      | k1_relat_1(sK6) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(sK6)
      | ~ sP0(sK7(sK6,X4),sK4) ) ),
    inference(subsumption_resolution,[],[f152,f38])).

fof(f152,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,sK7(sK6,X4)) != k1_funct_1(X4,sK7(sK6,X4))
      | sK6 = X4
      | k1_relat_1(sK6) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ sP0(sK7(sK6,X4),sK4) ) ),
    inference(superposition,[],[f45,f142])).

fof(f142,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,X0) = k1_funct_1(sK5,X0)
      | ~ sP0(X0,sK4) ) ),
    inference(subsumption_resolution,[],[f140,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK9(X0,X1)) = X0
          & r2_hidden(sK9(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK9(X0,X1)) = X0
        & r2_hidden(sK9(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f140,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,X0) = k1_funct_1(sK5,X0)
      | ~ r2_hidden(sK9(X0,sK4),k1_relat_1(sK4))
      | ~ sP0(X0,sK4) ) ),
    inference(superposition,[],[f135,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK9(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f135,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f134,f33])).

fof(f33,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f134,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f133,f34])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f133,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f132,f35])).

fof(f132,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_relat_1(sK5)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f131,f36])).

fof(f131,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f124,f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f124,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,sK5),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f123,f33])).

fof(f123,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,sK5),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f122,f34])).

fof(f122,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,sK5),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f121,f37])).

fof(f121,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,sK5),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f117,f38])).

fof(f117,plain,(
    ! [X0] :
      ( k1_funct_1(sK6,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,sK5),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f56,f42])).

fof(f42,plain,(
    k5_relat_1(sK4,sK5) = k5_relat_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f70,f33])).

fof(f70,plain,
    ( ~ v1_relat_1(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f69,f34])).

fof(f69,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl10_1 ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f11,f16,f15,f14])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f63,plain,
    ( ~ sP2(sK4)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl10_1
  <=> sP2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f68,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f59,f65,f61])).

fof(f59,plain,
    ( sP1(sK4,sK3)
    | ~ sP2(sK4) ),
    inference(superposition,[],[f57,f39])).

fof(f39,plain,(
    sK3 = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
