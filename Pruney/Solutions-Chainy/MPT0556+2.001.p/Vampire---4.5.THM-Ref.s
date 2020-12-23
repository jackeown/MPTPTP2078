%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:54 EST 2020

% Result     : Theorem 4.99s
% Output     : Refutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 155 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  272 ( 724 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4701,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4696,f46])).

fof(f46,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK5,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK4,sK5)
    & v1_relat_1(sK5)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(X3,sK3))
          & r1_tarski(sK2,sK3)
          & r1_tarski(sK4,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(X3,sK3))
        & r1_tarski(sK2,sK3)
        & r1_tarski(sK4,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK5,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK4,sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f4696,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f3237,f485])).

fof(f485,plain,(
    ! [X0] : ~ sP1(X0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f484,f44])).

fof(f44,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f484,plain,(
    ! [X0] :
      ( ~ sP1(X0,sK2,sK3)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f482,f45])).

fof(f45,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f482,plain,(
    ! [X0] :
      ( ~ sP1(X0,sK2,sK3)
      | ~ r1_tarski(sK4,sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f304,f238])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f51,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK4,X1),k9_relat_1(sK5,sK3))
      | ~ sP1(X0,sK2,X1) ) ),
    inference(superposition,[],[f297,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f23,f22])).

fof(f22,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f297,plain,(
    ! [X4] : ~ r1_tarski(k9_relat_1(sK4,k2_xboole_0(X4,sK2)),k9_relat_1(sK5,sK3)) ),
    inference(subsumption_resolution,[],[f296,f43])).

fof(f43,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f296,plain,(
    ! [X4] :
      ( ~ r1_tarski(k9_relat_1(sK4,k2_xboole_0(X4,sK2)),k9_relat_1(sK5,sK3))
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f284,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f284,plain,(
    ! [X2] : ~ r1_tarski(k2_xboole_0(X2,k9_relat_1(sK4,sK2)),k9_relat_1(sK5,sK3)) ),
    inference(resolution,[],[f130,f75])).

fof(f75,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f130,plain,(
    ! [X6] :
      ( ~ r1_tarski(k9_relat_1(sK4,sK2),X6)
      | ~ r1_tarski(X6,k9_relat_1(sK5,sK3)) ) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK5,sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f3237,plain,(
    ! [X4,X3] :
      ( sP1(X3,X4,X3)
      | ~ r1_tarski(X4,X3) ) ),
    inference(subsumption_resolution,[],[f3235,f941])).

fof(f941,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,X0),X1)
      | sP1(X0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f937,f313])).

fof(f313,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK7(X6,X7,X8),X8)
      | sP1(X6,X7,X8)
      | ~ r2_hidden(sK7(X6,X7,X8),X6) ) ),
    inference(resolution,[],[f65,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,sK7(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | ~ r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP0(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP0(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f937,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,X0),X0)
      | sP1(X0,X1,X0)
      | r2_hidden(sK7(X0,X1,X0),X1) ) ),
    inference(factoring,[],[f298])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | sP1(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f64,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK7(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3235,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK7(X3,X4,X3),X4)
      | sP1(X3,X4,X3)
      | ~ r1_tarski(X4,X3) ) ),
    inference(duplicate_literal_removal,[],[f3229])).

fof(f3229,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK7(X3,X4,X3),X4)
      | sP1(X3,X4,X3)
      | ~ r1_tarski(X4,X3)
      | sP1(X3,X4,X3) ) ),
    inference(resolution,[],[f810,f941])).

fof(f810,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X3)
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | sP1(X0,X1,X2)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f312,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f312,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK7(X3,X4,X5),X5)
      | sP1(X3,X4,X5)
      | ~ r2_hidden(sK7(X3,X4,X5),X4) ) ),
    inference(resolution,[],[f65,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (31179)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (31171)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (31168)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (31166)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (31177)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (31182)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (31174)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (31169)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (31193)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (31167)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (31188)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (31180)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (31189)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (31194)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (31190)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (31170)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (31191)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (31186)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (31181)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (31172)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (31185)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (31183)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (31178)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (31195)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (31173)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (31187)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (31176)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (31175)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (31192)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.58  % (31184)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 3.99/0.88  % (31171)Time limit reached!
% 3.99/0.88  % (31171)------------------------------
% 3.99/0.88  % (31171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/0.88  % (31171)Termination reason: Time limit
% 3.99/0.88  
% 3.99/0.88  % (31171)Memory used [KB]: 9083
% 3.99/0.88  % (31171)Time elapsed: 0.418 s
% 3.99/0.88  % (31171)------------------------------
% 3.99/0.88  % (31171)------------------------------
% 4.16/0.91  % (31183)Time limit reached!
% 4.16/0.91  % (31183)------------------------------
% 4.16/0.91  % (31183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.91  % (31183)Termination reason: Time limit
% 4.16/0.91  
% 4.16/0.91  % (31183)Memory used [KB]: 15095
% 4.16/0.91  % (31183)Time elapsed: 0.512 s
% 4.16/0.91  % (31183)------------------------------
% 4.16/0.91  % (31183)------------------------------
% 4.16/0.91  % (31178)Time limit reached!
% 4.16/0.91  % (31178)------------------------------
% 4.16/0.91  % (31178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.91  % (31178)Termination reason: Time limit
% 4.16/0.91  % (31178)Termination phase: Saturation
% 4.16/0.91  
% 4.16/0.91  % (31178)Memory used [KB]: 9594
% 4.16/0.91  % (31178)Time elapsed: 0.513 s
% 4.16/0.91  % (31178)------------------------------
% 4.16/0.91  % (31178)------------------------------
% 4.45/0.92  % (31167)Time limit reached!
% 4.45/0.92  % (31167)------------------------------
% 4.45/0.92  % (31167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.92  % (31167)Termination reason: Time limit
% 4.45/0.92  % (31167)Termination phase: Saturation
% 4.45/0.92  
% 4.45/0.92  % (31167)Memory used [KB]: 8059
% 4.45/0.92  % (31167)Time elapsed: 0.500 s
% 4.45/0.92  % (31167)------------------------------
% 4.45/0.92  % (31167)------------------------------
% 4.45/0.92  % (31176)Time limit reached!
% 4.45/0.92  % (31176)------------------------------
% 4.45/0.92  % (31176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.92  % (31176)Termination reason: Time limit
% 4.45/0.92  % (31176)Termination phase: Saturation
% 4.45/0.92  
% 4.45/0.92  % (31176)Memory used [KB]: 11257
% 4.45/0.92  % (31176)Time elapsed: 0.500 s
% 4.45/0.92  % (31176)------------------------------
% 4.45/0.92  % (31176)------------------------------
% 4.45/0.93  % (31166)Time limit reached!
% 4.45/0.93  % (31166)------------------------------
% 4.45/0.93  % (31166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.93  % (31166)Termination reason: Time limit
% 4.45/0.93  
% 4.45/0.93  % (31166)Memory used [KB]: 3070
% 4.45/0.93  % (31166)Time elapsed: 0.508 s
% 4.45/0.93  % (31166)------------------------------
% 4.45/0.93  % (31166)------------------------------
% 4.45/1.00  % (31173)Time limit reached!
% 4.45/1.00  % (31173)------------------------------
% 4.45/1.00  % (31173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.00  % (31173)Termination reason: Time limit
% 4.45/1.00  
% 4.45/1.00  % (31173)Memory used [KB]: 10874
% 4.45/1.00  % (31173)Time elapsed: 0.602 s
% 4.45/1.00  % (31173)------------------------------
% 4.45/1.00  % (31173)------------------------------
% 4.99/1.00  % (31182)Time limit reached!
% 4.99/1.00  % (31182)------------------------------
% 4.99/1.00  % (31182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.99/1.00  % (31182)Termination reason: Time limit
% 4.99/1.00  % (31182)Termination phase: Saturation
% 4.99/1.00  
% 4.99/1.00  % (31182)Memory used [KB]: 14839
% 4.99/1.00  % (31182)Time elapsed: 0.614 s
% 4.99/1.00  % (31182)------------------------------
% 4.99/1.00  % (31182)------------------------------
% 4.99/1.01  % (31194)Time limit reached!
% 4.99/1.01  % (31194)------------------------------
% 4.99/1.01  % (31194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.99/1.01  % (31194)Termination reason: Time limit
% 4.99/1.01  
% 4.99/1.01  % (31194)Memory used [KB]: 8827
% 4.99/1.01  % (31194)Time elapsed: 0.613 s
% 4.99/1.01  % (31194)------------------------------
% 4.99/1.01  % (31194)------------------------------
% 4.99/1.02  % (31198)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.99/1.03  % (31199)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.99/1.04  % (31197)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.99/1.06  % (31201)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.99/1.06  % (31193)Refutation found. Thanks to Tanya!
% 4.99/1.06  % SZS status Theorem for theBenchmark
% 4.99/1.06  % SZS output start Proof for theBenchmark
% 4.99/1.06  fof(f4701,plain,(
% 4.99/1.06    $false),
% 4.99/1.06    inference(subsumption_resolution,[],[f4696,f46])).
% 4.99/1.06  fof(f46,plain,(
% 4.99/1.06    r1_tarski(sK2,sK3)),
% 4.99/1.06    inference(cnf_transformation,[],[f27])).
% 4.99/1.06  fof(f27,plain,(
% 4.99/1.06    (~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK5,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK4,sK5) & v1_relat_1(sK5)) & v1_relat_1(sK4)),
% 4.99/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f26,f25])).
% 4.99/1.06  fof(f25,plain,(
% 4.99/1.06    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(X3,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK4,X3) & v1_relat_1(X3)) & v1_relat_1(sK4))),
% 4.99/1.06    introduced(choice_axiom,[])).
% 4.99/1.06  fof(f26,plain,(
% 4.99/1.06    ? [X3] : (~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(X3,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK4,X3) & v1_relat_1(X3)) => (~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK5,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK4,sK5) & v1_relat_1(sK5))),
% 4.99/1.06    introduced(choice_axiom,[])).
% 4.99/1.06  fof(f14,plain,(
% 4.99/1.06    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 4.99/1.06    inference(flattening,[],[f13])).
% 4.99/1.06  fof(f13,plain,(
% 4.99/1.06    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 4.99/1.06    inference(ennf_transformation,[],[f12])).
% 4.99/1.06  fof(f12,negated_conjecture,(
% 4.99/1.06    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 4.99/1.06    inference(negated_conjecture,[],[f11])).
% 4.99/1.06  fof(f11,conjecture,(
% 4.99/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).
% 4.99/1.06  fof(f4696,plain,(
% 4.99/1.06    ~r1_tarski(sK2,sK3)),
% 4.99/1.06    inference(resolution,[],[f3237,f485])).
% 4.99/1.06  fof(f485,plain,(
% 4.99/1.06    ( ! [X0] : (~sP1(X0,sK2,sK3)) )),
% 4.99/1.06    inference(subsumption_resolution,[],[f484,f44])).
% 4.99/1.06  fof(f44,plain,(
% 4.99/1.06    v1_relat_1(sK5)),
% 4.99/1.06    inference(cnf_transformation,[],[f27])).
% 4.99/1.06  fof(f484,plain,(
% 4.99/1.06    ( ! [X0] : (~sP1(X0,sK2,sK3) | ~v1_relat_1(sK5)) )),
% 4.99/1.06    inference(subsumption_resolution,[],[f482,f45])).
% 4.99/1.06  fof(f45,plain,(
% 4.99/1.06    r1_tarski(sK4,sK5)),
% 4.99/1.06    inference(cnf_transformation,[],[f27])).
% 4.99/1.06  fof(f482,plain,(
% 4.99/1.06    ( ! [X0] : (~sP1(X0,sK2,sK3) | ~r1_tarski(sK4,sK5) | ~v1_relat_1(sK5)) )),
% 4.99/1.06    inference(resolution,[],[f304,f238])).
% 4.99/1.06  fof(f238,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) )),
% 4.99/1.06    inference(subsumption_resolution,[],[f51,f83])).
% 4.99/1.06  fof(f83,plain,(
% 4.99/1.06    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 4.99/1.06    inference(resolution,[],[f48,f59])).
% 4.99/1.06  fof(f59,plain,(
% 4.99/1.06    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f34])).
% 4.99/1.06  fof(f34,plain,(
% 4.99/1.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.99/1.06    inference(nnf_transformation,[],[f7])).
% 4.99/1.06  fof(f7,axiom,(
% 4.99/1.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 4.99/1.06  fof(f48,plain,(
% 4.99/1.06    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f15])).
% 4.99/1.06  fof(f15,plain,(
% 4.99/1.06    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.99/1.06    inference(ennf_transformation,[],[f8])).
% 4.99/1.06  fof(f8,axiom,(
% 4.99/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 4.99/1.06  fof(f51,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f17])).
% 4.99/1.06  fof(f17,plain,(
% 4.99/1.06    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.99/1.06    inference(flattening,[],[f16])).
% 4.99/1.06  fof(f16,plain,(
% 4.99/1.06    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.99/1.06    inference(ennf_transformation,[],[f10])).
% 4.99/1.06  fof(f10,axiom,(
% 4.99/1.06    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 4.99/1.06  fof(f304,plain,(
% 4.99/1.06    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK4,X1),k9_relat_1(sK5,sK3)) | ~sP1(X0,sK2,X1)) )),
% 4.99/1.06    inference(superposition,[],[f297,f70])).
% 4.99/1.06  fof(f70,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f42])).
% 4.99/1.06  fof(f42,plain,(
% 4.99/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 4.99/1.06    inference(nnf_transformation,[],[f24])).
% 4.99/1.06  fof(f24,plain,(
% 4.99/1.06    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 4.99/1.06    inference(definition_folding,[],[f3,f23,f22])).
% 4.99/1.06  fof(f22,plain,(
% 4.99/1.06    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 4.99/1.06    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.99/1.06  fof(f23,plain,(
% 4.99/1.06    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 4.99/1.06    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.99/1.06  fof(f3,axiom,(
% 4.99/1.06    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 4.99/1.06  fof(f297,plain,(
% 4.99/1.06    ( ! [X4] : (~r1_tarski(k9_relat_1(sK4,k2_xboole_0(X4,sK2)),k9_relat_1(sK5,sK3))) )),
% 4.99/1.06    inference(subsumption_resolution,[],[f296,f43])).
% 4.99/1.06  fof(f43,plain,(
% 4.99/1.06    v1_relat_1(sK4)),
% 4.99/1.06    inference(cnf_transformation,[],[f27])).
% 4.99/1.06  fof(f296,plain,(
% 4.99/1.06    ( ! [X4] : (~r1_tarski(k9_relat_1(sK4,k2_xboole_0(X4,sK2)),k9_relat_1(sK5,sK3)) | ~v1_relat_1(sK4)) )),
% 4.99/1.06    inference(superposition,[],[f284,f60])).
% 4.99/1.06  fof(f60,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f19])).
% 4.99/1.06  fof(f19,plain,(
% 4.99/1.06    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 4.99/1.06    inference(ennf_transformation,[],[f9])).
% 4.99/1.06  fof(f9,axiom,(
% 4.99/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 4.99/1.06  fof(f284,plain,(
% 4.99/1.06    ( ! [X2] : (~r1_tarski(k2_xboole_0(X2,k9_relat_1(sK4,sK2)),k9_relat_1(sK5,sK3))) )),
% 4.99/1.06    inference(resolution,[],[f130,f75])).
% 4.99/1.06  fof(f75,plain,(
% 4.99/1.06    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 4.99/1.06    inference(superposition,[],[f49,f50])).
% 4.99/1.06  fof(f50,plain,(
% 4.99/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f1])).
% 4.99/1.06  fof(f1,axiom,(
% 4.99/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.99/1.06  fof(f49,plain,(
% 4.99/1.06    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.99/1.06    inference(cnf_transformation,[],[f6])).
% 4.99/1.06  fof(f6,axiom,(
% 4.99/1.06    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.99/1.06  fof(f130,plain,(
% 4.99/1.06    ( ! [X6] : (~r1_tarski(k9_relat_1(sK4,sK2),X6) | ~r1_tarski(X6,k9_relat_1(sK5,sK3))) )),
% 4.99/1.06    inference(resolution,[],[f61,f47])).
% 4.99/1.06  fof(f47,plain,(
% 4.99/1.06    ~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK5,sK3))),
% 4.99/1.06    inference(cnf_transformation,[],[f27])).
% 4.99/1.06  fof(f61,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f21])).
% 4.99/1.06  fof(f21,plain,(
% 4.99/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.99/1.06    inference(flattening,[],[f20])).
% 4.99/1.06  fof(f20,plain,(
% 4.99/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.99/1.06    inference(ennf_transformation,[],[f5])).
% 4.99/1.06  fof(f5,axiom,(
% 4.99/1.06    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.99/1.06  fof(f3237,plain,(
% 4.99/1.06    ( ! [X4,X3] : (sP1(X3,X4,X3) | ~r1_tarski(X4,X3)) )),
% 4.99/1.06    inference(subsumption_resolution,[],[f3235,f941])).
% 4.99/1.06  fof(f941,plain,(
% 4.99/1.06    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,X0),X1) | sP1(X0,X1,X0)) )),
% 4.99/1.06    inference(subsumption_resolution,[],[f937,f313])).
% 4.99/1.06  fof(f313,plain,(
% 4.99/1.06    ( ! [X6,X8,X7] : (~r2_hidden(sK7(X6,X7,X8),X8) | sP1(X6,X7,X8) | ~r2_hidden(sK7(X6,X7,X8),X6)) )),
% 4.99/1.06    inference(resolution,[],[f65,f67])).
% 4.99/1.06  fof(f67,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X2)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f41])).
% 4.99/1.06  fof(f41,plain,(
% 4.99/1.06    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP0(X0,X1,X2)))),
% 4.99/1.06    inference(rectify,[],[f40])).
% 4.99/1.06  fof(f40,plain,(
% 4.99/1.06    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP0(X1,X3,X0)))),
% 4.99/1.06    inference(flattening,[],[f39])).
% 4.99/1.06  fof(f39,plain,(
% 4.99/1.06    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 4.99/1.06    inference(nnf_transformation,[],[f22])).
% 4.99/1.06  fof(f65,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (~sP0(X1,sK7(X0,X1,X2),X0) | sP1(X0,X1,X2) | ~r2_hidden(sK7(X0,X1,X2),X2)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f38])).
% 4.99/1.06  fof(f38,plain,(
% 4.99/1.06    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 4.99/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).
% 4.99/1.06  fof(f37,plain,(
% 4.99/1.06    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 4.99/1.06    introduced(choice_axiom,[])).
% 4.99/1.06  fof(f36,plain,(
% 4.99/1.06    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 4.99/1.06    inference(rectify,[],[f35])).
% 4.99/1.06  fof(f35,plain,(
% 4.99/1.06    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 4.99/1.06    inference(nnf_transformation,[],[f23])).
% 4.99/1.06  fof(f937,plain,(
% 4.99/1.06    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,X0),X0) | sP1(X0,X1,X0) | r2_hidden(sK7(X0,X1,X0),X1)) )),
% 4.99/1.06    inference(factoring,[],[f298])).
% 4.99/1.06  fof(f298,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | sP1(X0,X1,X2) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X1)) )),
% 4.99/1.06    inference(resolution,[],[f64,f66])).
% 4.99/1.06  fof(f66,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2) | r2_hidden(X1,X0)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f41])).
% 4.99/1.06  fof(f64,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (sP0(X1,sK7(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK7(X0,X1,X2),X2)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f38])).
% 4.99/1.06  fof(f3235,plain,(
% 4.99/1.06    ( ! [X4,X3] : (~r2_hidden(sK7(X3,X4,X3),X4) | sP1(X3,X4,X3) | ~r1_tarski(X4,X3)) )),
% 4.99/1.06    inference(duplicate_literal_removal,[],[f3229])).
% 4.99/1.06  fof(f3229,plain,(
% 4.99/1.06    ( ! [X4,X3] : (~r2_hidden(sK7(X3,X4,X3),X4) | sP1(X3,X4,X3) | ~r1_tarski(X4,X3) | sP1(X3,X4,X3)) )),
% 4.99/1.06    inference(resolution,[],[f810,f941])).
% 4.99/1.06  fof(f810,plain,(
% 4.99/1.06    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK7(X0,X1,X2),X3) | ~r2_hidden(sK7(X0,X1,X2),X1) | sP1(X0,X1,X2) | ~r1_tarski(X3,X2)) )),
% 4.99/1.06    inference(resolution,[],[f312,f55])).
% 4.99/1.06  fof(f55,plain,(
% 4.99/1.06    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f33])).
% 4.99/1.06  fof(f33,plain,(
% 4.99/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.99/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).
% 4.99/1.06  fof(f32,plain,(
% 4.99/1.06    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 4.99/1.06    introduced(choice_axiom,[])).
% 4.99/1.06  fof(f31,plain,(
% 4.99/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.99/1.06    inference(rectify,[],[f30])).
% 4.99/1.06  fof(f30,plain,(
% 4.99/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.99/1.06    inference(nnf_transformation,[],[f18])).
% 4.99/1.06  fof(f18,plain,(
% 4.99/1.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.99/1.06    inference(ennf_transformation,[],[f2])).
% 4.99/1.06  fof(f2,axiom,(
% 4.99/1.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.99/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 4.99/1.06  fof(f312,plain,(
% 4.99/1.06    ( ! [X4,X5,X3] : (~r2_hidden(sK7(X3,X4,X5),X5) | sP1(X3,X4,X5) | ~r2_hidden(sK7(X3,X4,X5),X4)) )),
% 4.99/1.06    inference(resolution,[],[f65,f68])).
% 4.99/1.06  fof(f68,plain,(
% 4.99/1.06    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 4.99/1.06    inference(cnf_transformation,[],[f41])).
% 4.99/1.06  % SZS output end Proof for theBenchmark
% 4.99/1.06  % (31193)------------------------------
% 4.99/1.06  % (31193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.99/1.06  % (31193)Termination reason: Refutation
% 4.99/1.06  
% 4.99/1.06  % (31193)Memory used [KB]: 8571
% 4.99/1.06  % (31193)Time elapsed: 0.655 s
% 4.99/1.06  % (31193)------------------------------
% 4.99/1.06  % (31193)------------------------------
% 4.99/1.07  % (31165)Success in time 0.719 s
%------------------------------------------------------------------------------
