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
% DateTime   : Thu Dec  3 13:00:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 (3719 expanded)
%              Number of leaves         :   19 (1113 expanded)
%              Depth                    :   44
%              Number of atoms          :  518 (15462 expanded)
%              Number of equality atoms :   96 (3272 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(global_subsumption,[],[f56,f53,f290,f314])).

fof(f314,plain,
    ( ~ v3_ordinal1(sK2)
    | ~ r1_ordinal1(sK2,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f312,f182])).

fof(f182,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK3)
      | ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK3)
      | sK3 = X1 ) ),
    inference(resolution,[],[f177,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f177,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_ordinal1(sK3))
      | ~ r1_ordinal1(X1,sK3)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( sK2 != sK3
    & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK2 != X1
          & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( sK2 != X1
        & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK2 != sK3
      & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f312,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(global_subsumption,[],[f166,f311])).

fof(f311,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r2_hidden(sK2,sK3) ),
    inference(backward_demodulation,[],[f278,f309])).

fof(f309,plain,(
    k1_wellord2(sK2) = k2_wellord1(k1_wellord2(sK3),sK2) ),
    inference(resolution,[],[f297,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f297,plain,(
    r1_tarski(sK2,sK3) ),
    inference(global_subsumption,[],[f53,f296])).

fof(f296,plain,
    ( r1_tarski(sK2,sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[],[f290,f112])).

fof(f112,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(X1,sK3)
      | r1_tarski(X1,sK3)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f77,f54])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f278,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2))
    | ~ r2_hidden(sK2,sK3) ),
    inference(global_subsumption,[],[f54,f277])).

fof(f277,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2))
    | ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3) ),
    inference(superposition,[],[f260,f276])).

fof(f276,plain,(
    sK2 = k1_wellord1(k1_wellord2(sK3),sK2) ),
    inference(global_subsumption,[],[f56,f54,f211,f274])).

fof(f274,plain,
    ( sK2 = k1_wellord1(k1_wellord2(sK3),sK2)
    | ~ v3_ordinal1(sK3)
    | ~ r1_ordinal1(sK3,sK2)
    | sK2 = sK3 ),
    inference(resolution,[],[f273,f179])).

fof(f179,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK2)
      | sK2 = X1 ) ),
    inference(resolution,[],[f176,f82])).

fof(f176,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_ordinal1(sK2))
      | ~ r1_ordinal1(X0,sK2)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f64,f53])).

fof(f273,plain,
    ( ~ r2_hidden(sK3,sK2)
    | sK2 = k1_wellord1(k1_wellord2(sK3),sK2) ),
    inference(global_subsumption,[],[f55,f272])).

fof(f272,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ r2_hidden(sK3,sK2)
    | sK2 = k1_wellord1(k1_wellord2(sK3),sK2) ),
    inference(superposition,[],[f271,f216])).

fof(f216,plain,
    ( k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3)
    | sK2 = k1_wellord1(k1_wellord2(sK3),sK2) ),
    inference(resolution,[],[f213,f76])).

fof(f213,plain,
    ( r1_tarski(sK3,sK2)
    | sK2 = k1_wellord1(k1_wellord2(sK3),sK2) ),
    inference(global_subsumption,[],[f54,f212])).

fof(f212,plain,
    ( sK2 = k1_wellord1(k1_wellord2(sK3),sK2)
    | r1_tarski(sK3,sK2)
    | ~ v3_ordinal1(sK3) ),
    inference(resolution,[],[f211,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK2)
      | r1_tarski(X0,sK2)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f77,f53])).

fof(f271,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3))
    | ~ r2_hidden(sK3,sK2) ),
    inference(global_subsumption,[],[f53,f270])).

fof(f270,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3))
    | ~ r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK2) ),
    inference(superposition,[],[f260,f269])).

fof(f269,plain,(
    sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(global_subsumption,[],[f56,f53,f199,f267])).

fof(f267,plain,
    ( sK3 = k1_wellord1(k1_wellord2(sK2),sK3)
    | ~ v3_ordinal1(sK2)
    | ~ r1_ordinal1(sK2,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f266,f182])).

fof(f266,plain,
    ( ~ r2_hidden(sK2,sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(global_subsumption,[],[f166,f265])).

fof(f265,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r2_hidden(sK2,sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r2_hidden(sK2,sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(superposition,[],[f262,f202])).

fof(f202,plain,
    ( k1_wellord2(sK2) = k2_wellord1(k1_wellord2(sK3),sK2)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(resolution,[],[f201,f76])).

fof(f201,plain,
    ( r1_tarski(sK2,sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(global_subsumption,[],[f53,f200])).

fof(f200,plain,
    ( sK3 = k1_wellord1(k1_wellord2(sK2),sK3)
    | r1_tarski(sK2,sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[],[f199,f112])).

fof(f262,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2))
    | ~ r2_hidden(sK2,sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(global_subsumption,[],[f54,f261])).

fof(f261,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2))
    | ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(superposition,[],[f260,f214])).

fof(f214,plain,
    ( sK2 = k1_wellord1(k1_wellord2(sK3),sK2)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(resolution,[],[f213,f204])).

fof(f204,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(global_subsumption,[],[f56,f203])).

fof(f203,plain,
    ( sK3 = k1_wellord1(k1_wellord2(sK2),sK3)
    | sK2 = sK3
    | ~ r1_tarski(sK3,sK2) ),
    inference(resolution,[],[f201,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f199,plain,
    ( r1_ordinal1(sK2,sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    inference(global_subsumption,[],[f54,f53,f196])).

fof(f196,plain,
    ( sK3 = k1_wellord1(k1_wellord2(sK2),sK3)
    | ~ v3_ordinal1(sK3)
    | r1_ordinal1(sK2,sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[],[f192,f103])).

fof(f103,plain,(
    ! [X1] :
      ( r2_hidden(sK3,X1)
      | r1_ordinal1(X1,sK3)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f61,f54])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f192,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_wellord1(k1_wellord2(sK2),X0) = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f62,f53])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f55,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f211,plain,
    ( r1_ordinal1(sK3,sK2)
    | sK2 = k1_wellord1(k1_wellord2(sK3),sK2) ),
    inference(global_subsumption,[],[f54,f53,f207])).

fof(f207,plain,
    ( sK2 = k1_wellord1(k1_wellord2(sK3),sK2)
    | ~ v3_ordinal1(sK2)
    | r1_ordinal1(sK3,sK2)
    | ~ v3_ordinal1(sK3) ),
    inference(resolution,[],[f193,f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK2,X0)
      | r1_ordinal1(X0,sK2)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f61,f53])).

fof(f193,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | k1_wellord1(k1_wellord2(sK3),X1) = X1
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f62,f54])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(global_subsumption,[],[f57,f259])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f258,f95])).

fof(f95,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f67,f94])).

fof(f94,plain,(
    ! [X0] : sP0(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f85,f93])).

fof(f93,plain,(
    ! [X0,X1] : sP1(X0,k1_wellord2(X1)) ),
    inference(resolution,[],[f74,f57])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f29,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
            <=> r1_tarski(X2,X3) )
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f85,plain,(
    ! [X0] :
      ( sP0(k1_wellord2(X0),X0)
      | ~ sP1(X0,k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k1_wellord2(X0) != X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X0) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X0) )
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f58,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f166,plain,(
    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) ),
    inference(resolution,[],[f165,f55])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
      | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) ) ),
    inference(resolution,[],[f101,f57])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r4_wellord1(k1_wellord2(X1),X0)
      | ~ r4_wellord1(X0,k1_wellord2(X1)) ) ),
    inference(resolution,[],[f59,f57])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f290,plain,(
    r1_ordinal1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f136,f288])).

fof(f288,plain,(
    ~ r1_ordinal1(sK3,sK2) ),
    inference(global_subsumption,[],[f56,f54,f286])).

fof(f286,plain,
    ( ~ v3_ordinal1(sK3)
    | ~ r1_ordinal1(sK3,sK2)
    | sK2 = sK3 ),
    inference(resolution,[],[f285,f179])).

fof(f285,plain,(
    ~ r2_hidden(sK3,sK2) ),
    inference(global_subsumption,[],[f55,f284])).

fof(f284,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ r2_hidden(sK3,sK2) ),
    inference(backward_demodulation,[],[f271,f283])).

fof(f283,plain,(
    k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3) ),
    inference(global_subsumption,[],[f56,f53,f98,f138,f142,f281])).

fof(f281,plain,
    ( k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3)
    | ~ v3_ordinal1(sK2)
    | ~ r1_ordinal1(sK2,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f280,f182])).

fof(f280,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3) ),
    inference(global_subsumption,[],[f166,f279])).

fof(f279,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r2_hidden(sK2,sK3)
    | k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3) ),
    inference(superposition,[],[f278,f163])).

fof(f163,plain,
    ( k1_wellord2(sK2) = k2_wellord1(k1_wellord2(sK3),sK2)
    | k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3) ),
    inference(resolution,[],[f142,f76])).

fof(f142,plain,
    ( r1_tarski(sK2,sK3)
    | k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3) ),
    inference(resolution,[],[f140,f76])).

fof(f140,plain,
    ( r1_tarski(sK3,sK2)
    | r1_tarski(sK2,sK3) ),
    inference(global_subsumption,[],[f53,f139])).

fof(f139,plain,
    ( r1_tarski(sK3,sK2)
    | r1_tarski(sK2,sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[],[f138,f112])).

fof(f138,plain,
    ( r1_ordinal1(sK2,sK3)
    | r1_tarski(sK3,sK2) ),
    inference(global_subsumption,[],[f54,f137])).

fof(f137,plain,
    ( r1_ordinal1(sK2,sK3)
    | r1_tarski(sK3,sK2)
    | ~ v3_ordinal1(sK3) ),
    inference(resolution,[],[f136,f111])).

fof(f98,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3) ),
    inference(extensionality_resolution,[],[f81,f56])).

fof(f136,plain,
    ( r1_ordinal1(sK3,sK2)
    | r1_ordinal1(sK2,sK3) ),
    inference(global_subsumption,[],[f53,f134])).

fof(f134,plain,
    ( r1_ordinal1(sK3,sK2)
    | r1_ordinal1(sK2,sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[],[f130,f103])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r1_ordinal1(X0,sK2) ) ),
    inference(global_subsumption,[],[f96,f126])).

fof(f126,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,sK2)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f123,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_ordinal1(sK2))
      | r1_ordinal1(X0,sK2)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f63,f53])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f75,f53])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f53,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (21622)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (21622)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (21630)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f316,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(global_subsumption,[],[f56,f53,f290,f314])).
% 0.20/0.49  fof(f314,plain,(
% 0.20/0.49    ~v3_ordinal1(sK2) | ~r1_ordinal1(sK2,sK3) | sK2 = sK3),
% 0.20/0.49    inference(resolution,[],[f312,f182])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ( ! [X1] : (r2_hidden(X1,sK3) | ~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK3) | sK3 = X1) )),
% 0.20/0.49    inference(resolution,[],[f177,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.49    inference(flattening,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(sK3)) | ~r1_ordinal1(X1,sK3) | ~v3_ordinal1(X1)) )),
% 0.20/0.49    inference(resolution,[],[f64,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    v3_ordinal1(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f39,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f14])).
% 0.20/0.49  fof(f14,conjecture,(
% 0.20/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.49  fof(f312,plain,(
% 0.20/0.49    ~r2_hidden(sK2,sK3)),
% 0.20/0.49    inference(global_subsumption,[],[f166,f311])).
% 0.20/0.49  fof(f311,plain,(
% 0.20/0.49    ~r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) | ~r2_hidden(sK2,sK3)),
% 0.20/0.49    inference(backward_demodulation,[],[f278,f309])).
% 0.20/0.49  fof(f309,plain,(
% 0.20/0.49    k1_wellord2(sK2) = k2_wellord1(k1_wellord2(sK3),sK2)),
% 0.20/0.49    inference(resolution,[],[f297,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    r1_tarski(sK2,sK3)),
% 0.20/0.49    inference(global_subsumption,[],[f53,f296])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    r1_tarski(sK2,sK3) | ~v3_ordinal1(sK2)),
% 0.20/0.49    inference(resolution,[],[f290,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ( ! [X1] : (~r1_ordinal1(X1,sK3) | r1_tarski(X1,sK3) | ~v3_ordinal1(X1)) )),
% 0.20/0.49    inference(resolution,[],[f77,f54])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    ~r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) | ~r2_hidden(sK2,sK3)),
% 0.20/0.49    inference(global_subsumption,[],[f54,f277])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    ~r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) | ~r2_hidden(sK2,sK3) | ~v3_ordinal1(sK3)),
% 0.20/0.49    inference(superposition,[],[f260,f276])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    sK2 = k1_wellord1(k1_wellord2(sK3),sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f56,f54,f211,f274])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    sK2 = k1_wellord1(k1_wellord2(sK3),sK2) | ~v3_ordinal1(sK3) | ~r1_ordinal1(sK3,sK2) | sK2 = sK3),
% 0.20/0.50    inference(resolution,[],[f273,f179])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ( ! [X1] : (r2_hidden(X1,sK2) | ~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK2) | sK2 = X1) )),
% 0.20/0.50    inference(resolution,[],[f176,f82])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(sK2)) | ~r1_ordinal1(X0,sK2) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f64,f53])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    ~r2_hidden(sK3,sK2) | sK2 = k1_wellord1(k1_wellord2(sK3),sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f55,f272])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) | ~r2_hidden(sK3,sK2) | sK2 = k1_wellord1(k1_wellord2(sK3),sK2)),
% 0.20/0.50    inference(superposition,[],[f271,f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3) | sK2 = k1_wellord1(k1_wellord2(sK3),sK2)),
% 0.20/0.50    inference(resolution,[],[f213,f76])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    r1_tarski(sK3,sK2) | sK2 = k1_wellord1(k1_wellord2(sK3),sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f54,f212])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    sK2 = k1_wellord1(k1_wellord2(sK3),sK2) | r1_tarski(sK3,sK2) | ~v3_ordinal1(sK3)),
% 0.20/0.50    inference(resolution,[],[f211,f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_ordinal1(X0,sK2) | r1_tarski(X0,sK2) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f77,f53])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) | ~r2_hidden(sK3,sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f53,f270])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) | ~r2_hidden(sK3,sK2) | ~v3_ordinal1(sK2)),
% 0.20/0.50    inference(superposition,[],[f260,f269])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f56,f53,f199,f267])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    sK3 = k1_wellord1(k1_wellord2(sK2),sK3) | ~v3_ordinal1(sK2) | ~r1_ordinal1(sK2,sK3) | sK2 = sK3),
% 0.20/0.50    inference(resolution,[],[f266,f182])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    ~r2_hidden(sK2,sK3) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f166,f265])).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) | ~r2_hidden(sK2,sK3) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f263])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) | ~r2_hidden(sK2,sK3) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(superposition,[],[f262,f202])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    k1_wellord2(sK2) = k2_wellord1(k1_wellord2(sK3),sK2) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(resolution,[],[f201,f76])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    r1_tarski(sK2,sK3) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f53,f200])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    sK3 = k1_wellord1(k1_wellord2(sK2),sK3) | r1_tarski(sK2,sK3) | ~v3_ordinal1(sK2)),
% 0.20/0.50    inference(resolution,[],[f199,f112])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) | ~r2_hidden(sK2,sK3) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f54,f261])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) | ~r2_hidden(sK2,sK3) | ~v3_ordinal1(sK3) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(superposition,[],[f260,f214])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    sK2 = k1_wellord1(k1_wellord2(sK3),sK2) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(resolution,[],[f213,f204])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ~r1_tarski(sK3,sK2) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f56,f203])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    sK3 = k1_wellord1(k1_wellord2(sK2),sK3) | sK2 = sK3 | ~r1_tarski(sK3,sK2)),
% 0.20/0.50    inference(resolution,[],[f201,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    r1_ordinal1(sK2,sK3) | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f54,f53,f196])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    sK3 = k1_wellord1(k1_wellord2(sK2),sK3) | ~v3_ordinal1(sK3) | r1_ordinal1(sK2,sK3) | ~v3_ordinal1(sK2)),
% 0.20/0.50    inference(resolution,[],[f192,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X1] : (r2_hidden(sK3,X1) | r1_ordinal1(X1,sK3) | ~v3_ordinal1(X1)) )),
% 0.20/0.50    inference(resolution,[],[f61,f54])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_wellord1(k1_wellord2(sK2),X0) = X0 | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f62,f53])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    r1_ordinal1(sK3,sK2) | sK2 = k1_wellord1(k1_wellord2(sK3),sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f54,f53,f207])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    sK2 = k1_wellord1(k1_wellord2(sK3),sK2) | ~v3_ordinal1(sK2) | r1_ordinal1(sK3,sK2) | ~v3_ordinal1(sK3)),
% 0.20/0.50    inference(resolution,[],[f193,f102])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK2,X0) | r1_ordinal1(X0,sK2) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f61,f53])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(X1,sK3) | k1_wellord1(k1_wellord2(sK3),X1) = X1 | ~v3_ordinal1(X1)) )),
% 0.20/0.50    inference(resolution,[],[f62,f54])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.20/0.50    inference(global_subsumption,[],[f57,f259])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f258,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.50    inference(resolution,[],[f67,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X0] : (sP0(k1_wellord2(X0),X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f85,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP1(X0,k1_wellord2(X1))) )),
% 0.20/0.50    inference(resolution,[],[f74,f57])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | sP1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(definition_folding,[],[f29,f36,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0] : (sP0(k1_wellord2(X0),X0) | ~sP1(X0,k1_wellord2(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP0(X1,X0) | k1_wellord2(X0) != X1 | ~sP1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_wellord2(X0) != X1)) | ~sP1(X0,X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f36])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~sP0(X0,X1) | k3_relat_1(X0) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.20/0.50    inference(flattening,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X1,X0] : ((sP0(X1,X0) | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f35])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.20/0.50    inference(resolution,[],[f58,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))),
% 0.20/0.50    inference(resolution,[],[f165,f55])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) )),
% 0.20/0.50    inference(resolution,[],[f101,f57])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | r4_wellord1(k1_wellord2(X1),X0) | ~r4_wellord1(X0,k1_wellord2(X1))) )),
% 0.20/0.50    inference(resolution,[],[f59,f57])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    r1_ordinal1(sK2,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f136,f288])).
% 0.20/0.50  fof(f288,plain,(
% 0.20/0.50    ~r1_ordinal1(sK3,sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f56,f54,f286])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    ~v3_ordinal1(sK3) | ~r1_ordinal1(sK3,sK2) | sK2 = sK3),
% 0.20/0.50    inference(resolution,[],[f285,f179])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    ~r2_hidden(sK3,sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f55,f284])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) | ~r2_hidden(sK3,sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f271,f283])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f56,f53,f98,f138,f142,f281])).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3) | ~v3_ordinal1(sK2) | ~r1_ordinal1(sK2,sK3) | sK2 = sK3),
% 0.20/0.50    inference(resolution,[],[f280,f182])).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    ~r2_hidden(sK2,sK3) | k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f166,f279])).
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) | ~r2_hidden(sK2,sK3) | k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(superposition,[],[f278,f163])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    k1_wellord2(sK2) = k2_wellord1(k1_wellord2(sK3),sK2) | k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(resolution,[],[f142,f76])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    r1_tarski(sK2,sK3) | k1_wellord2(sK3) = k2_wellord1(k1_wellord2(sK2),sK3)),
% 0.20/0.50    inference(resolution,[],[f140,f76])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    r1_tarski(sK3,sK2) | r1_tarski(sK2,sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f53,f139])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    r1_tarski(sK3,sK2) | r1_tarski(sK2,sK3) | ~v3_ordinal1(sK2)),
% 0.20/0.50    inference(resolution,[],[f138,f112])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    r1_ordinal1(sK2,sK3) | r1_tarski(sK3,sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f54,f137])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    r1_ordinal1(sK2,sK3) | r1_tarski(sK3,sK2) | ~v3_ordinal1(sK3)),
% 0.20/0.50    inference(resolution,[],[f136,f111])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ~r1_tarski(sK3,sK2) | ~r1_tarski(sK2,sK3)),
% 0.20/0.50    inference(extensionality_resolution,[],[f81,f56])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    r1_ordinal1(sK3,sK2) | r1_ordinal1(sK2,sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f53,f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    r1_ordinal1(sK3,sK2) | r1_ordinal1(sK2,sK3) | ~v3_ordinal1(sK2)),
% 0.20/0.50    inference(resolution,[],[f130,f103])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | r1_ordinal1(X0,sK2)) )),
% 0.20/0.50    inference(global_subsumption,[],[f96,f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X0] : (r1_ordinal1(X0,sK2) | ~v3_ordinal1(X0) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.50    inference(resolution,[],[f123,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f52])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k1_ordinal1(sK2)) | r1_ordinal1(X0,sK2) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f63,f53])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | v3_ordinal1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f75,f53])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    v3_ordinal1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    sK2 != sK3),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (21622)------------------------------
% 0.20/0.50  % (21622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21622)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (21622)Memory used [KB]: 6396
% 0.20/0.50  % (21622)Time elapsed: 0.079 s
% 0.20/0.50  % (21622)------------------------------
% 0.20/0.50  % (21622)------------------------------
% 0.20/0.50  % (21609)Success in time 0.144 s
%------------------------------------------------------------------------------
