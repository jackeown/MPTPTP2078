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

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 238 expanded)
%              Number of leaves         :   15 (  64 expanded)
%              Depth                    :   19
%              Number of atoms          :  464 (1401 expanded)
%              Number of equality atoms :  122 ( 424 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f101,f133,f137,f149,f164,f191])).

fof(f191,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f189,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
      | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21])).

fof(f21,plain,
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

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f189,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(resolution,[],[f173,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f51,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f173,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f172,f28])).

fof(f172,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f171,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f171,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f170,f30])).

fof(f30,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f170,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(superposition,[],[f163,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f77,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f77,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f61,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k1_relat_1(X1)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f26])).

fof(f26,plain,(
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

fof(f25,plain,(
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
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f163,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_6
  <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f164,plain,
    ( ~ spl4_3
    | ~ spl4_6
    | spl4_5 ),
    inference(avatar_split_clause,[],[f160,f131,f162,f125])).

fof(f125,plain,
    ( spl4_3
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f131,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f160,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_5 ),
    inference(subsumption_resolution,[],[f159,f28])).

fof(f159,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f158,f31])).

fof(f31,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f158,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(superposition,[],[f132,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f132,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f149,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f147,f28])).

fof(f147,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f146,f29])).

fof(f146,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_4 ),
    inference(resolution,[],[f129,f36])).

fof(f129,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_4
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f137,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f135,f28])).

fof(f135,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f134,f29])).

fof(f134,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(resolution,[],[f126,f35])).

fof(f126,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f133,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f123,f66,f63,f131,f128,f125])).

fof(f63,plain,
    ( spl4_1
  <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f66,plain,
    ( spl4_2
  <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f123,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f122,f28])).

fof(f122,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f115,f29])).

fof(f115,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(superposition,[],[f67,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f67,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f101,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f99,f28])).

fof(f99,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f98,f29])).

fof(f98,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f97,f30])).

fof(f97,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f94,f31])).

fof(f94,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(superposition,[],[f64,f70])).

fof(f70,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f69,f35])).

fof(f69,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f68,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f32,f66,f63])).

fof(f32,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (9156)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (9151)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (9146)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (9149)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (9157)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (9148)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (9146)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f68,f101,f133,f137,f149,f164,f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    $false | spl4_6),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    (sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.48    inference(resolution,[],[f173,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(superposition,[],[f51,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f172,f28])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f171,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f170,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v2_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(superposition,[],[f163,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f77,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f61,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(X0) = k1_relat_1(X1) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) => (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(rectify,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl4_6 <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ~spl4_3 | ~spl4_6 | spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f160,f131,f162,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl4_3 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl4_5 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f159,f28])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f158,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.49    inference(superposition,[],[f132,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f131])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    $false | spl4_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f147,f28])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl4_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f146,f29])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_4),
% 0.21/0.49    inference(resolution,[],[f129,f36])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK1)) | spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl4_4 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    $false | spl4_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f135,f28])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl4_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f134,f29])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_3),
% 0.21/0.49    inference(resolution,[],[f126,f35])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK1)) | spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_1 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f123,f66,f63,f131,f128,f125])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl4_1 <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl4_2 <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f28])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f115,f29])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.49    inference(superposition,[],[f67,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    $false | spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f28])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f29])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f30])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f31])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    sK0 != sK0 | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.49    inference(superposition,[],[f64,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f69,f35])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f54,f36])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X5,X1] : (k1_funct_1(X1,k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X4,X0,X5,X1] : (k1_funct_1(X1,X4) = X5 | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f66,f63])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (9146)------------------------------
% 0.21/0.49  % (9146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9146)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (9146)Memory used [KB]: 10746
% 0.21/0.49  % (9146)Time elapsed: 0.074 s
% 0.21/0.49  % (9146)------------------------------
% 0.21/0.49  % (9146)------------------------------
% 0.21/0.49  % (9147)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (9140)Success in time 0.129 s
%------------------------------------------------------------------------------
