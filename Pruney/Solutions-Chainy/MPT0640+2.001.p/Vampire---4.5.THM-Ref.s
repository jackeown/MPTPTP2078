%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 485 expanded)
%              Number of leaves         :   11 ( 151 expanded)
%              Depth                    :   20
%              Number of atoms          :  350 (3309 expanded)
%              Number of equality atoms :   68 ( 225 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f780,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f121,f779])).

fof(f779,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f778])).

fof(f778,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f777,f71])).

fof(f71,plain,(
    sK2(sK1) != sK3(sK1) ),
    inference(subsumption_resolution,[],[f70,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_funct_1(sK1)
    & r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    & v2_funct_1(k5_relat_1(sK1,sK0))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
            & v2_funct_1(k5_relat_1(X1,X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(sK0))
          & v2_funct_1(k5_relat_1(X1,sK0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ v2_funct_1(X1)
        & r1_tarski(k2_relat_1(X1),k1_relat_1(sK0))
        & v2_funct_1(k5_relat_1(X1,sK0))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(sK1)
      & r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
      & v2_funct_1(k5_relat_1(sK1,sK0))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v2_funct_1(k5_relat_1(X1,X0)) )
             => v2_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f70,plain,
    ( sK2(sK1) != sK3(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f67,f33])).

fof(f33,plain,(
    ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,
    ( sK2(sK1) != sK3(sK1)
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sK2(X0) != sK3(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK2(X0) != sK3(X0)
            & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK2(X0) != sK3(X0)
        & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f777,plain,
    ( sK2(sK1) = sK3(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f776,f266])).

fof(f266,plain,(
    k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) ),
    inference(forward_demodulation,[],[f265,f83])).

fof(f83,plain,(
    k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1)) ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f82,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f79,f33])).

fof(f79,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f265,plain,(
    k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK3(sK1))) ),
    inference(resolution,[],[f104,f65])).

fof(f65,plain,(
    r2_hidden(sK3(sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f64,f29])).

fof(f64,plain,
    ( r2_hidden(sK3(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f61,f33])).

fof(f61,plain,
    ( r2_hidden(sK3(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f37,f30])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f103,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f102,f28])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f29])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f30])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f42,f86])).

fof(f86,plain,(
    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f85,f29])).

fof(f85,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f84,f27])).

fof(f84,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f776,plain,
    ( k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) != k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1))
    | sK2(sK1) = sK3(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f269,f65])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X0 )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f267,f264])).

fof(f264,plain,(
    k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) ),
    inference(resolution,[],[f104,f59])).

fof(f59,plain,(
    r2_hidden(sK2(sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f58,f29])).

fof(f58,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f47,f33])).

fof(f47,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f36,f30])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | sK2(sK1) = X0
        | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f113,f59])).

fof(f113,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | X1 = X2
        | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_4
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | X1 = X2
        | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f121,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f119,f29])).

fof(f119,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f117,f110])).

fof(f110,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_3
  <=> v1_funct_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f117,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f76,f30])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k5_relat_1(X0,sK0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_1(k5_relat_1(X0,sK0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f114,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f106,f112,f108])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
      | X1 = X2
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0)) ) ),
    inference(subsumption_resolution,[],[f105,f92])).

fof(f92,plain,(
    v1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,sK0)) ) ),
    inference(resolution,[],[f43,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
      | X1 = X2
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0)) ) ),
    inference(subsumption_resolution,[],[f99,f31])).

fof(f31,plain,(
    v2_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
      | X1 = X2
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(k5_relat_1(sK1,sK0))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0)) ) ),
    inference(superposition,[],[f35,f86])).

fof(f35,plain,(
    ! [X4,X0,X3] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:13:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (7424)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.43  % (7432)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.44  % (7424)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f780,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f114,f121,f779])).
% 0.22/0.45  fof(f779,plain,(
% 0.22/0.45    ~spl4_4),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f778])).
% 0.22/0.45  fof(f778,plain,(
% 0.22/0.45    $false | ~spl4_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f777,f71])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    sK2(sK1) != sK3(sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f70,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    v1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    (~v2_funct_1(sK1) & r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) & v2_funct_1(k5_relat_1(sK1,sK0)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f21,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~v2_funct_1(X1) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_funct_1(X1) & r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) & v2_funct_1(k5_relat_1(X1,sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ? [X1] : (~v2_funct_1(X1) & r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) & v2_funct_1(k5_relat_1(X1,sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_funct_1(sK1) & r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) & v2_funct_1(k5_relat_1(sK1,sK0)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~v2_funct_1(X1) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((~v2_funct_1(X1) & (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    sK2(sK1) != sK3(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f67,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ~v2_funct_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    sK2(sK1) != sK3(sK1) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(resolution,[],[f39,f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    v1_funct_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_funct_1(X0) | sK2(X0) != sK3(X0) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0] : (((v2_funct_1(X0) | (sK2(X0) != sK3(X0) & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0)) & r2_hidden(sK3(X0),k1_relat_1(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK2(X0) != sK3(X0) & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0)) & r2_hidden(sK3(X0),k1_relat_1(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(rectify,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.22/0.45  fof(f777,plain,(
% 0.22/0.45    sK2(sK1) = sK3(sK1) | ~spl4_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f776,f266])).
% 0.22/0.45  fof(f266,plain,(
% 0.22/0.45    k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1))),
% 0.22/0.45    inference(forward_demodulation,[],[f265,f83])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))),
% 0.22/0.45    inference(subsumption_resolution,[],[f82,f29])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f79,f33])).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(resolution,[],[f38,f30])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f265,plain,(
% 0.22/0.45    k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK3(sK1)))),
% 0.22/0.45    inference(resolution,[],[f104,f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    r2_hidden(sK3(sK1),k1_relat_1(sK1))),
% 0.22/0.45    inference(subsumption_resolution,[],[f64,f29])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    r2_hidden(sK3(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f61,f33])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    r2_hidden(sK3(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(resolution,[],[f37,f30])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK3(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f103,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    v1_relat_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f103,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0)) | ~v1_relat_1(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f102,f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    v1_funct_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f102,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f101,f29])).
% 0.22/0.45  fof(f101,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f98,f30])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.22/0.45    inference(superposition,[],[f42,f86])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f85,f29])).
% 0.22/0.45  fof(f85,plain,(
% 0.22/0.45    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f84,f27])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(resolution,[],[f34,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.22/0.45  fof(f776,plain,(
% 0.22/0.45    k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) != k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) | sK2(sK1) = sK3(sK1) | ~spl4_4),
% 0.22/0.45    inference(resolution,[],[f269,f65])).
% 0.22/0.45  fof(f269,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) | sK2(sK1) = X0) ) | ~spl4_4),
% 0.22/0.45    inference(forward_demodulation,[],[f267,f264])).
% 0.22/0.45  fof(f264,plain,(
% 0.22/0.45    k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))),
% 0.22/0.45    inference(resolution,[],[f104,f59])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    r2_hidden(sK2(sK1),k1_relat_1(sK1))),
% 0.22/0.45    inference(subsumption_resolution,[],[f58,f29])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    r2_hidden(sK2(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f47,f33])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    r2_hidden(sK2(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(resolution,[],[f36,f30])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f267,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK2(sK1) = X0 | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1))) ) | ~spl4_4),
% 0.22/0.45    inference(resolution,[],[f113,f59])).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    ( ! [X2,X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | X1 = X2 | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1)) ) | ~spl4_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f112])).
% 0.22/0.45  fof(f112,plain,(
% 0.22/0.45    spl4_4 <=> ! [X1,X2] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | X1 = X2 | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    spl4_3),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    $false | spl4_3),
% 0.22/0.45    inference(subsumption_resolution,[],[f119,f29])).
% 0.22/0.45  fof(f119,plain,(
% 0.22/0.45    ~v1_relat_1(sK1) | spl4_3),
% 0.22/0.45    inference(subsumption_resolution,[],[f117,f110])).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    ~v1_funct_1(k5_relat_1(sK1,sK0)) | spl4_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f108])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    spl4_3 <=> v1_funct_1(k5_relat_1(sK1,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.45  fof(f117,plain,(
% 0.22/0.45    v1_funct_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(resolution,[],[f76,f30])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k5_relat_1(X0,sK0)) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f74,f27])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    ( ! [X0] : (v1_funct_1(k5_relat_1(X0,sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(resolution,[],[f41,f28])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_funct_1(X1) | v1_funct_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ~spl4_3 | spl4_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f106,f112,f108])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    ( ! [X2,X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | X1 = X2 | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_funct_1(k5_relat_1(sK1,sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f105,f92])).
% 0.22/0.45  fof(f92,plain,(
% 0.22/0.45    v1_relat_1(k5_relat_1(sK1,sK0))),
% 0.22/0.45    inference(resolution,[],[f44,f29])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,sK0))) )),
% 0.22/0.45    inference(resolution,[],[f43,f27])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.45  fof(f105,plain,(
% 0.22/0.45    ( ! [X2,X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | X1 = X2 | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_funct_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(k5_relat_1(sK1,sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f99,f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    v2_funct_1(k5_relat_1(sK1,sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f99,plain,(
% 0.22/0.45    ( ! [X2,X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK0),X2) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | X1 = X2 | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(k5_relat_1(sK1,sK0)) | ~v1_funct_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(k5_relat_1(sK1,sK0))) )),
% 0.22/0.45    inference(superposition,[],[f35,f86])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X4,X0,X3] : (~r2_hidden(X4,k1_relat_1(X0)) | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (7424)------------------------------
% 0.22/0.45  % (7424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (7424)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (7424)Memory used [KB]: 11001
% 0.22/0.45  % (7424)Time elapsed: 0.053 s
% 0.22/0.45  % (7424)------------------------------
% 0.22/0.45  % (7424)------------------------------
% 0.22/0.46  % (7413)Success in time 0.095 s
%------------------------------------------------------------------------------
