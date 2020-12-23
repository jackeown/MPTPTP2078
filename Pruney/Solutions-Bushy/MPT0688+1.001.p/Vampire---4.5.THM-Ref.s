%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0688+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:28 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   27 (  51 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 180 expanded)
%              Number of equality atoms :   14 (  35 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31,f24])).

fof(f24,plain,(
    r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f17,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    & ! [X2] :
        ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
        | ~ r2_hidden(X2,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(X1))
        & ! [X2] :
            ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
            | ~ r2_hidden(X2,X0) )
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k2_relat_1(sK1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
          | ~ r2_hidden(X2,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

fof(f31,plain,(
    ~ r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ~ r2_hidden(sK2(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f29,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f16,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f16,plain,(
    ! [X2] :
      ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
