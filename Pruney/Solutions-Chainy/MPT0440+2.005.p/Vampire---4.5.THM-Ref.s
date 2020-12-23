%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:57 EST 2020

% Result     : Theorem 14.97s
% Output     : Refutation 15.24s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 443 expanded)
%              Number of leaves         :   24 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          :  393 (1118 expanded)
%              Number of equality atoms :  128 ( 567 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17535,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f187,f200,f15228,f17534])).

fof(f17534,plain,
    ( spl11_1
    | ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f17533])).

fof(f17533,plain,
    ( $false
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f17520,f145])).

fof(f145,plain,
    ( k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl11_1
  <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f17520,plain,
    ( k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl11_2 ),
    inference(superposition,[],[f17081,f15248])).

fof(f15248,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK2))
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f10576,f148])).

fof(f148,plain,
    ( k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl11_2
  <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f10576,plain,(
    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f122,f114])).

fof(f114,plain,(
    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f64,f112])).

fof(f112,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k1_tarski(sK1) != k2_relat_1(sK2)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2 )
   => ( ( k1_tarski(sK1) != k2_relat_1(sK2)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2 ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f122,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f100,f112,f73,f73])).

fof(f100,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f17081,plain,
    ( ! [X0] : k1_relat_1(k2_zfmisc_1(X0,k2_relat_1(sK2))) = X0
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f17075,f15587])).

fof(f15587,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(sK8(k2_zfmisc_1(X13,k2_relat_1(sK2)),X14),X13)
        | k1_relat_1(k2_zfmisc_1(X13,k2_relat_1(sK2))) = X14
        | ~ r2_hidden(sK8(k2_zfmisc_1(X13,k2_relat_1(sK2)),X14),X14) )
    | ~ spl11_2 ),
    inference(resolution,[],[f15383,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
      | k1_relat_1(X0) = X1
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f15383,plain,
    ( ! [X26,X25] :
        ( r2_hidden(k4_tarski(X25,sK1),k2_zfmisc_1(X26,k2_relat_1(sK2)))
        | ~ r2_hidden(X25,X26) )
    | ~ spl11_2 ),
    inference(superposition,[],[f138,f148])).

fof(f138,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f104,f112])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f17075,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(k2_zfmisc_1(X0,k2_relat_1(sK2)),X0),X0)
        | k1_relat_1(k2_zfmisc_1(X0,k2_relat_1(sK2))) = X0 )
    | ~ spl11_2 ),
    inference(factoring,[],[f15477])).

fof(f15477,plain,
    ( ! [X10,X9] :
        ( r2_hidden(sK8(k2_zfmisc_1(X9,k2_relat_1(sK2)),X10),X10)
        | r2_hidden(sK8(k2_zfmisc_1(X9,k2_relat_1(sK2)),X10),X9)
        | k1_relat_1(k2_zfmisc_1(X9,k2_relat_1(sK2))) = X10 )
    | ~ spl11_2 ),
    inference(resolution,[],[f15376,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f15376,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X6,k2_relat_1(sK2)))
        | r2_hidden(X4,X6) )
    | ~ spl11_2 ),
    inference(superposition,[],[f125,f148])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f102,f112])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f15228,plain,
    ( spl11_2
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f15227])).

fof(f15227,plain,
    ( $false
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f15218,f11303])).

fof(f11303,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl11_4 ),
    inference(resolution,[],[f214,f134])).

fof(f134,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f48,f47,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f214,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl11_4 ),
    inference(superposition,[],[f186,f114])).

fof(f186,plain,
    ( ! [X0] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl11_4
  <=> ! [X0] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f15218,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl11_2
    | ~ spl11_4 ),
    inference(resolution,[],[f15213,f135])).

fof(f135,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15213,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK1),sK2)
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f15212,f186])).

fof(f15212,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),sK2)
        | ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) )
    | spl11_2 ),
    inference(subsumption_resolution,[],[f15211,f149])).

fof(f149,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f15211,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),sK2)
        | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
        | ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) )
    | spl11_2 ),
    inference(superposition,[],[f90,f14264])).

fof(f14264,plain,
    ( sK1 = sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl11_2 ),
    inference(subsumption_resolution,[],[f14263,f10902])).

fof(f10902,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK1 = X1 ) ),
    inference(superposition,[],[f130,f10576])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f109,f112,f112])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f14263,plain,
    ( sK1 = sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k4_tarski(sK0,sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | spl11_2 ),
    inference(subsumption_resolution,[],[f14237,f149])).

fof(f14237,plain,
    ( k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK1 = sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k4_tarski(sK0,sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) ),
    inference(resolution,[],[f11268,f10909])).

fof(f10909,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k2_enumset1(sK1,sK1,sK1,sK1))
      | r2_hidden(k4_tarski(sK0,X8),sK2) ) ),
    inference(superposition,[],[f139,f10576])).

fof(f139,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(definition_unfolding,[],[f107,f112])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f11268,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),X0)
      | k2_relat_1(sK2) = X0
      | sK1 = sK5(sK2,X0) ) ),
    inference(resolution,[],[f10902,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f200,plain,(
    ~ spl11_3 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f198,f197])).

fof(f197,plain,
    ( k1_xboole_0 != sK2
    | ~ spl11_3 ),
    inference(backward_demodulation,[],[f174,f195])).

fof(f195,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(sK2,X0)
    | ~ spl11_3 ),
    inference(resolution,[],[f189,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f189,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl11_3 ),
    inference(resolution,[],[f183,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f183,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl11_3
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f174,plain,(
    sK2 != k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f171,f151])).

fof(f151,plain,(
    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f114,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f101,f73,f112,f73])).

fof(f101,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f171,plain,(
    k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) != k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    inference(resolution,[],[f155,f141])).

fof(f141,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X0 != X2 ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(definition_unfolding,[],[f110,f112,f112])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK0,sK1),X0)
      | k4_xboole_0(X0,sK2) != X0 ) ),
    inference(superposition,[],[f119,f114])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f97,f112])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f198,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_3 ),
    inference(backward_demodulation,[],[f194,f195])).

fof(f194,plain,
    ( ! [X5] : sK2 = k4_xboole_0(sK2,k2_enumset1(X5,X5,X5,X5))
    | ~ spl11_3 ),
    inference(resolution,[],[f183,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f98,f112])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f187,plain,
    ( spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f175,f185,f182])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f157,f139])).

fof(f157,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X6,sK2))
      | r2_hidden(X4,X6) ) ),
    inference(superposition,[],[f125,f114])).

fof(f150,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f113,f147,f143])).

fof(f113,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f65,f112,f112])).

fof(f65,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:09:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (27997)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (27990)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (28005)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (27993)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (27994)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (27989)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.52  % (27992)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.52  % (27998)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.23/0.53  % (27999)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.23/0.53  % (28014)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.23/0.53  % (28006)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.53  % (28006)Refutation not found, incomplete strategy% (28006)------------------------------
% 1.23/0.53  % (28006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (28011)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.53  % (28006)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (28006)Memory used [KB]: 10618
% 1.23/0.53  % (28006)Time elapsed: 0.111 s
% 1.23/0.53  % (28006)------------------------------
% 1.23/0.53  % (28006)------------------------------
% 1.23/0.53  % (28001)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.53  % (28007)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.53  % (28003)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.53  % (28002)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.53  % (28012)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.23/0.53  % (27999)Refutation not found, incomplete strategy% (27999)------------------------------
% 1.23/0.53  % (27999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (27999)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (27999)Memory used [KB]: 10618
% 1.23/0.53  % (27999)Time elapsed: 0.127 s
% 1.23/0.53  % (27999)------------------------------
% 1.23/0.53  % (27999)------------------------------
% 1.23/0.54  % (27991)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.54  % (28009)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.54  % (27995)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.54  % (28018)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.54  % (28016)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (28015)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (27996)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.55  % (28017)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.55  % (28004)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.55  % (28010)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (28008)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (28013)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.56  % (28000)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.96/0.65  % (28032)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.96/0.67  % (28034)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.03/0.79  % (28034)Refutation not found, incomplete strategy% (28034)------------------------------
% 3.03/0.79  % (28034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.79  % (28034)Termination reason: Refutation not found, incomplete strategy
% 3.03/0.80  
% 3.03/0.80  % (28034)Memory used [KB]: 6268
% 3.03/0.80  % (28034)Time elapsed: 0.206 s
% 3.03/0.80  % (28034)------------------------------
% 3.03/0.80  % (28034)------------------------------
% 3.39/0.83  % (27994)Time limit reached!
% 3.39/0.83  % (27994)------------------------------
% 3.39/0.83  % (27994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.84  % (27994)Termination reason: Time limit
% 3.62/0.84  
% 3.62/0.84  % (27994)Memory used [KB]: 8827
% 3.62/0.84  % (27994)Time elapsed: 0.428 s
% 3.62/0.84  % (27994)------------------------------
% 3.62/0.84  % (27994)------------------------------
% 3.62/0.91  % (28001)Time limit reached!
% 3.62/0.91  % (28001)------------------------------
% 3.62/0.91  % (28001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.91  % (28001)Termination reason: Time limit
% 3.62/0.91  % (28001)Termination phase: Saturation
% 3.62/0.91  
% 3.62/0.91  % (28001)Memory used [KB]: 8827
% 3.62/0.91  % (28001)Time elapsed: 0.500 s
% 3.62/0.91  % (28001)------------------------------
% 3.62/0.91  % (28001)------------------------------
% 3.62/0.92  % (27989)Time limit reached!
% 3.62/0.92  % (27989)------------------------------
% 3.62/0.92  % (27989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.92  % (27989)Termination reason: Time limit
% 3.62/0.92  
% 3.62/0.92  % (27989)Memory used [KB]: 4221
% 3.62/0.92  % (27989)Time elapsed: 0.509 s
% 3.62/0.92  % (27989)------------------------------
% 3.62/0.92  % (27989)------------------------------
% 4.22/0.93  % (27990)Time limit reached!
% 4.22/0.93  % (27990)------------------------------
% 4.22/0.93  % (27990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.93  % (28169)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.22/0.94  % (27990)Termination reason: Time limit
% 4.22/0.94  
% 4.22/0.94  % (27990)Memory used [KB]: 10106
% 4.22/0.94  % (27990)Time elapsed: 0.517 s
% 4.22/0.94  % (27990)------------------------------
% 4.22/0.94  % (27990)------------------------------
% 4.22/0.96  % (28178)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.63/1.01  % (28200)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.63/1.02  % (27996)Time limit reached!
% 4.63/1.02  % (27996)------------------------------
% 4.63/1.02  % (27996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.02  % (27996)Termination reason: Time limit
% 4.63/1.02  
% 4.63/1.02  % (27996)Memory used [KB]: 11001
% 4.63/1.02  % (27996)Time elapsed: 0.611 s
% 4.63/1.02  % (27996)------------------------------
% 4.63/1.02  % (27996)------------------------------
% 4.63/1.02  % (28005)Time limit reached!
% 4.63/1.02  % (28005)------------------------------
% 4.63/1.02  % (28005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.02  % (28005)Termination reason: Time limit
% 4.63/1.02  
% 4.63/1.02  % (28005)Memory used [KB]: 18293
% 4.63/1.02  % (28005)Time elapsed: 0.619 s
% 4.63/1.02  % (28005)------------------------------
% 4.63/1.02  % (28005)------------------------------
% 4.63/1.03  % (28017)Time limit reached!
% 4.63/1.03  % (28017)------------------------------
% 4.63/1.03  % (28017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.03  % (28017)Termination reason: Time limit
% 4.63/1.03  % (28017)Termination phase: Saturation
% 4.63/1.03  
% 4.63/1.03  % (28017)Memory used [KB]: 10362
% 4.63/1.03  % (28017)Time elapsed: 0.600 s
% 4.63/1.03  % (28017)------------------------------
% 4.63/1.03  % (28017)------------------------------
% 4.63/1.04  % (28205)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.13/1.06  % (28213)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.92/1.13  % (28256)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.10/1.17  % (28254)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.10/1.19  % (28257)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.10/1.21  % (28010)Time limit reached!
% 6.10/1.21  % (28010)------------------------------
% 6.10/1.21  % (28010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.10/1.21  % (28010)Termination reason: Time limit
% 6.10/1.21  
% 6.10/1.21  % (28010)Memory used [KB]: 6268
% 6.10/1.21  % (28010)Time elapsed: 0.812 s
% 6.10/1.21  % (28010)------------------------------
% 6.10/1.21  % (28010)------------------------------
% 7.18/1.32  % (28178)Time limit reached!
% 7.18/1.32  % (28178)------------------------------
% 7.18/1.32  % (28178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.18/1.32  % (28178)Termination reason: Time limit
% 7.18/1.32  % (28178)Termination phase: Saturation
% 7.18/1.32  
% 7.18/1.32  % (28178)Memory used [KB]: 7547
% 7.18/1.32  % (28178)Time elapsed: 0.400 s
% 7.18/1.32  % (28178)------------------------------
% 7.18/1.32  % (28178)------------------------------
% 7.18/1.34  % (28258)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.73/1.37  % (28200)Time limit reached!
% 7.73/1.37  % (28200)------------------------------
% 7.73/1.37  % (28200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.73/1.37  % (28200)Termination reason: Time limit
% 7.73/1.37  
% 7.73/1.37  % (28200)Memory used [KB]: 13560
% 7.73/1.37  % (28200)Time elapsed: 0.423 s
% 7.73/1.37  % (28200)------------------------------
% 7.73/1.37  % (28200)------------------------------
% 8.22/1.42  % (27991)Time limit reached!
% 8.22/1.42  % (27991)------------------------------
% 8.22/1.42  % (27991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.22/1.44  % (28259)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.22/1.44  % (27991)Termination reason: Time limit
% 8.22/1.44  % (27991)Termination phase: Saturation
% 8.22/1.44  
% 8.22/1.44  % (27991)Memory used [KB]: 17910
% 8.22/1.44  % (27991)Time elapsed: 1.0000 s
% 8.22/1.44  % (27991)------------------------------
% 8.22/1.44  % (27991)------------------------------
% 8.47/1.48  % (28260)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.02/1.56  % (28261)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.36/1.63  % (28015)Time limit reached!
% 9.36/1.63  % (28015)------------------------------
% 9.36/1.63  % (28015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.36/1.63  % (28015)Termination reason: Time limit
% 9.36/1.63  % (28015)Termination phase: Saturation
% 9.36/1.63  
% 9.36/1.63  % (28015)Memory used [KB]: 14839
% 9.36/1.63  % (28015)Time elapsed: 1.221 s
% 9.36/1.63  % (28015)------------------------------
% 9.36/1.63  % (28015)------------------------------
% 10.28/1.66  % (28011)Time limit reached!
% 10.28/1.66  % (28011)------------------------------
% 10.28/1.66  % (28011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.28/1.66  % (28011)Termination reason: Time limit
% 10.28/1.66  % (28011)Termination phase: Saturation
% 10.28/1.66  
% 10.28/1.66  % (28011)Memory used [KB]: 19061
% 10.28/1.66  % (28011)Time elapsed: 1.222 s
% 10.28/1.66  % (28011)------------------------------
% 10.28/1.66  % (28011)------------------------------
% 10.79/1.73  % (28013)Time limit reached!
% 10.79/1.73  % (28013)------------------------------
% 10.79/1.73  % (28013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.79/1.73  % (28013)Termination reason: Time limit
% 10.79/1.73  
% 10.79/1.73  % (28013)Memory used [KB]: 19189
% 10.79/1.73  % (28013)Time elapsed: 1.319 s
% 10.79/1.73  % (28013)------------------------------
% 10.79/1.73  % (28013)------------------------------
% 10.92/1.76  % (28004)Time limit reached!
% 10.92/1.76  % (28004)------------------------------
% 10.92/1.76  % (28004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.92/1.76  % (28004)Termination reason: Time limit
% 10.92/1.76  
% 10.92/1.76  % (28004)Memory used [KB]: 14839
% 10.92/1.76  % (28004)Time elapsed: 1.321 s
% 10.92/1.76  % (28004)------------------------------
% 10.92/1.76  % (28004)------------------------------
% 10.92/1.76  % (28262)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 10.92/1.77  % (28263)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.78/1.88  % (28264)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.78/1.89  % (28260)Time limit reached!
% 11.78/1.89  % (28260)------------------------------
% 11.78/1.89  % (28260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.78/1.89  % (28260)Termination reason: Time limit
% 11.78/1.89  % (28260)Termination phase: Saturation
% 11.78/1.89  
% 11.78/1.89  % (28260)Memory used [KB]: 3454
% 11.78/1.89  % (28260)Time elapsed: 0.500 s
% 11.78/1.89  % (28260)------------------------------
% 11.78/1.89  % (28260)------------------------------
% 11.78/1.89  % (28265)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.78/1.92  % (28016)Time limit reached!
% 11.78/1.92  % (28016)------------------------------
% 11.78/1.92  % (28016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.78/1.93  % (28016)Termination reason: Time limit
% 11.78/1.93  
% 11.78/1.93  % (28016)Memory used [KB]: 14456
% 11.78/1.93  % (28016)Time elapsed: 1.511 s
% 11.78/1.93  % (28016)------------------------------
% 11.78/1.93  % (28016)------------------------------
% 11.78/1.94  % (27993)Time limit reached!
% 11.78/1.94  % (27993)------------------------------
% 11.78/1.94  % (27993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.78/1.94  % (27993)Termination reason: Time limit
% 11.78/1.94  
% 11.78/1.94  % (27993)Memory used [KB]: 13432
% 11.78/1.94  % (27993)Time elapsed: 1.531 s
% 11.78/1.94  % (27993)------------------------------
% 11.78/1.94  % (27993)------------------------------
% 12.58/2.02  % (28267)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 12.58/2.02  % (28000)Time limit reached!
% 12.58/2.02  % (28000)------------------------------
% 12.58/2.02  % (28000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.58/2.02  % (28266)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.58/2.02  % (28000)Termination reason: Time limit
% 12.58/2.02  % (28000)Termination phase: Saturation
% 12.58/2.02  
% 12.58/2.02  % (28000)Memory used [KB]: 26481
% 12.58/2.02  % (28000)Time elapsed: 1.600 s
% 12.58/2.02  % (28000)------------------------------
% 12.58/2.02  % (28000)------------------------------
% 13.01/2.08  % (28268)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.40/2.15  % (28264)Time limit reached!
% 13.40/2.15  % (28264)------------------------------
% 13.40/2.15  % (28264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.40/2.15  % (28264)Termination reason: Time limit
% 13.40/2.15  % (28264)Termination phase: Saturation
% 13.40/2.15  
% 13.40/2.15  % (28264)Memory used [KB]: 4221
% 13.40/2.15  % (28264)Time elapsed: 0.400 s
% 13.40/2.15  % (28264)------------------------------
% 13.40/2.15  % (28264)------------------------------
% 13.40/2.16  % (28269)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 14.33/2.19  % (28213)Time limit reached!
% 14.33/2.19  % (28213)------------------------------
% 14.33/2.19  % (28213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.33/2.19  % (28213)Termination reason: Time limit
% 14.33/2.19  
% 14.33/2.19  % (28213)Memory used [KB]: 12409
% 14.33/2.19  % (28213)Time elapsed: 1.219 s
% 14.33/2.19  % (28213)------------------------------
% 14.33/2.19  % (28213)------------------------------
% 14.97/2.27  % (28003)Time limit reached!
% 14.97/2.27  % (28003)------------------------------
% 14.97/2.27  % (28003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.97/2.27  % (28003)Termination reason: Time limit
% 14.97/2.27  
% 14.97/2.27  % (28003)Memory used [KB]: 8571
% 14.97/2.27  % (28003)Time elapsed: 1.821 s
% 14.97/2.27  % (28003)------------------------------
% 14.97/2.27  % (28003)------------------------------
% 14.97/2.27  % (27997)Refutation found. Thanks to Tanya!
% 14.97/2.27  % SZS status Theorem for theBenchmark
% 14.97/2.29  % (28270)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.24/2.29  % SZS output start Proof for theBenchmark
% 15.24/2.29  fof(f17535,plain,(
% 15.24/2.29    $false),
% 15.24/2.29    inference(avatar_sat_refutation,[],[f150,f187,f200,f15228,f17534])).
% 15.24/2.29  fof(f17534,plain,(
% 15.24/2.29    spl11_1 | ~spl11_2),
% 15.24/2.29    inference(avatar_contradiction_clause,[],[f17533])).
% 15.24/2.29  fof(f17533,plain,(
% 15.24/2.29    $false | (spl11_1 | ~spl11_2)),
% 15.24/2.29    inference(subsumption_resolution,[],[f17520,f145])).
% 15.24/2.29  fof(f145,plain,(
% 15.24/2.29    k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) | spl11_1),
% 15.24/2.29    inference(avatar_component_clause,[],[f143])).
% 15.24/2.29  fof(f143,plain,(
% 15.24/2.29    spl11_1 <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 15.24/2.29    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 15.24/2.29  fof(f17520,plain,(
% 15.24/2.29    k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl11_2),
% 15.24/2.29    inference(superposition,[],[f17081,f15248])).
% 15.24/2.29  fof(f15248,plain,(
% 15.24/2.29    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK2)) | ~spl11_2),
% 15.24/2.29    inference(backward_demodulation,[],[f10576,f148])).
% 15.24/2.29  fof(f148,plain,(
% 15.24/2.29    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl11_2),
% 15.24/2.29    inference(avatar_component_clause,[],[f147])).
% 15.24/2.29  fof(f147,plain,(
% 15.24/2.29    spl11_2 <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 15.24/2.29    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 15.24/2.29  fof(f10576,plain,(
% 15.24/2.29    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 15.24/2.29    inference(superposition,[],[f122,f114])).
% 15.24/2.29  fof(f114,plain,(
% 15.24/2.29    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 15.24/2.29    inference(definition_unfolding,[],[f64,f112])).
% 15.24/2.29  fof(f112,plain,(
% 15.24/2.29    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 15.24/2.29    inference(definition_unfolding,[],[f68,f73])).
% 15.24/2.29  fof(f73,plain,(
% 15.24/2.29    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f16])).
% 15.24/2.29  fof(f16,axiom,(
% 15.24/2.29    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 15.24/2.29  fof(f68,plain,(
% 15.24/2.29    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f15])).
% 15.24/2.29  fof(f15,axiom,(
% 15.24/2.29    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 15.24/2.29  fof(f64,plain,(
% 15.24/2.29    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 15.24/2.29    inference(cnf_transformation,[],[f34])).
% 15.24/2.29  fof(f34,plain,(
% 15.24/2.29    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 15.24/2.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33])).
% 15.24/2.29  fof(f33,plain,(
% 15.24/2.29    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)))),
% 15.24/2.29    introduced(choice_axiom,[])).
% 15.24/2.29  fof(f29,plain,(
% 15.24/2.29    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2)),
% 15.24/2.29    inference(ennf_transformation,[],[f28])).
% 15.24/2.29  fof(f28,plain,(
% 15.24/2.29    ~! [X0,X1,X2] : (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2)))),
% 15.24/2.29    inference(pure_predicate_removal,[],[f25])).
% 15.24/2.29  fof(f25,negated_conjecture,(
% 15.24/2.29    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 15.24/2.29    inference(negated_conjecture,[],[f24])).
% 15.24/2.29  fof(f24,conjecture,(
% 15.24/2.29    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 15.24/2.29  fof(f122,plain,(
% 15.24/2.29    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 15.24/2.29    inference(definition_unfolding,[],[f100,f112,f73,f73])).
% 15.24/2.29  fof(f100,plain,(
% 15.24/2.29    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 15.24/2.29    inference(cnf_transformation,[],[f20])).
% 15.24/2.29  fof(f20,axiom,(
% 15.24/2.29    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 15.24/2.29  fof(f17081,plain,(
% 15.24/2.29    ( ! [X0] : (k1_relat_1(k2_zfmisc_1(X0,k2_relat_1(sK2))) = X0) ) | ~spl11_2),
% 15.24/2.29    inference(subsumption_resolution,[],[f17075,f15587])).
% 15.24/2.29  fof(f15587,plain,(
% 15.24/2.29    ( ! [X14,X13] : (~r2_hidden(sK8(k2_zfmisc_1(X13,k2_relat_1(sK2)),X14),X13) | k1_relat_1(k2_zfmisc_1(X13,k2_relat_1(sK2))) = X14 | ~r2_hidden(sK8(k2_zfmisc_1(X13,k2_relat_1(sK2)),X14),X14)) ) | ~spl11_2),
% 15.24/2.29    inference(resolution,[],[f15383,f94])).
% 15.24/2.29  fof(f94,plain,(
% 15.24/2.29    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | k1_relat_1(X0) = X1 | ~r2_hidden(sK8(X0,X1),X1)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f55])).
% 15.24/2.29  fof(f55,plain,(
% 15.24/2.29    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 15.24/2.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f51,f54,f53,f52])).
% 15.24/2.29  fof(f52,plain,(
% 15.24/2.29    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 15.24/2.29    introduced(choice_axiom,[])).
% 15.24/2.29  fof(f53,plain,(
% 15.24/2.29    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0))),
% 15.24/2.29    introduced(choice_axiom,[])).
% 15.24/2.29  fof(f54,plain,(
% 15.24/2.29    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0))),
% 15.24/2.29    introduced(choice_axiom,[])).
% 15.24/2.29  fof(f51,plain,(
% 15.24/2.29    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 15.24/2.29    inference(rectify,[],[f50])).
% 15.24/2.29  fof(f50,plain,(
% 15.24/2.29    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 15.24/2.29    inference(nnf_transformation,[],[f22])).
% 15.24/2.29  fof(f22,axiom,(
% 15.24/2.29    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 15.24/2.29  fof(f15383,plain,(
% 15.24/2.29    ( ! [X26,X25] : (r2_hidden(k4_tarski(X25,sK1),k2_zfmisc_1(X26,k2_relat_1(sK2))) | ~r2_hidden(X25,X26)) ) | ~spl11_2),
% 15.24/2.29    inference(superposition,[],[f138,f148])).
% 15.24/2.29  fof(f138,plain,(
% 15.24/2.29    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 15.24/2.29    inference(equality_resolution,[],[f123])).
% 15.24/2.29  fof(f123,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 15.24/2.29    inference(definition_unfolding,[],[f104,f112])).
% 15.24/2.29  fof(f104,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f59])).
% 15.24/2.29  fof(f59,plain,(
% 15.24/2.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 15.24/2.29    inference(flattening,[],[f58])).
% 15.24/2.29  fof(f58,plain,(
% 15.24/2.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 15.24/2.29    inference(nnf_transformation,[],[f18])).
% 15.24/2.29  fof(f18,axiom,(
% 15.24/2.29    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 15.24/2.29  fof(f17075,plain,(
% 15.24/2.29    ( ! [X0] : (r2_hidden(sK8(k2_zfmisc_1(X0,k2_relat_1(sK2)),X0),X0) | k1_relat_1(k2_zfmisc_1(X0,k2_relat_1(sK2))) = X0) ) | ~spl11_2),
% 15.24/2.29    inference(factoring,[],[f15477])).
% 15.24/2.29  fof(f15477,plain,(
% 15.24/2.29    ( ! [X10,X9] : (r2_hidden(sK8(k2_zfmisc_1(X9,k2_relat_1(sK2)),X10),X10) | r2_hidden(sK8(k2_zfmisc_1(X9,k2_relat_1(sK2)),X10),X9) | k1_relat_1(k2_zfmisc_1(X9,k2_relat_1(sK2))) = X10) ) | ~spl11_2),
% 15.24/2.29    inference(resolution,[],[f15376,f93])).
% 15.24/2.29  fof(f93,plain,(
% 15.24/2.29    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK8(X0,X1),X1)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f55])).
% 15.24/2.29  fof(f15376,plain,(
% 15.24/2.29    ( ! [X6,X4,X5] : (~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X6,k2_relat_1(sK2))) | r2_hidden(X4,X6)) ) | ~spl11_2),
% 15.24/2.29    inference(superposition,[],[f125,f148])).
% 15.24/2.29  fof(f125,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | r2_hidden(X0,X2)) )),
% 15.24/2.29    inference(definition_unfolding,[],[f102,f112])).
% 15.24/2.29  fof(f102,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 15.24/2.29    inference(cnf_transformation,[],[f59])).
% 15.24/2.29  fof(f15228,plain,(
% 15.24/2.29    spl11_2 | ~spl11_4),
% 15.24/2.29    inference(avatar_contradiction_clause,[],[f15227])).
% 15.24/2.29  fof(f15227,plain,(
% 15.24/2.29    $false | (spl11_2 | ~spl11_4)),
% 15.24/2.29    inference(subsumption_resolution,[],[f15218,f11303])).
% 15.24/2.29  fof(f11303,plain,(
% 15.24/2.29    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl11_4),
% 15.24/2.29    inference(resolution,[],[f214,f134])).
% 15.24/2.29  fof(f134,plain,(
% 15.24/2.29    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 15.24/2.29    inference(equality_resolution,[],[f88])).
% 15.24/2.29  fof(f88,plain,(
% 15.24/2.29    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 15.24/2.29    inference(cnf_transformation,[],[f49])).
% 15.24/2.29  fof(f49,plain,(
% 15.24/2.29    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.24/2.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f48,f47,f46])).
% 15.24/2.29  fof(f46,plain,(
% 15.24/2.29    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 15.24/2.29    introduced(choice_axiom,[])).
% 15.24/2.29  fof(f47,plain,(
% 15.24/2.29    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 15.24/2.29    introduced(choice_axiom,[])).
% 15.24/2.29  fof(f48,plain,(
% 15.24/2.29    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 15.24/2.29    introduced(choice_axiom,[])).
% 15.24/2.29  fof(f45,plain,(
% 15.24/2.29    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.24/2.29    inference(rectify,[],[f44])).
% 15.24/2.29  fof(f44,plain,(
% 15.24/2.29    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 15.24/2.29    inference(nnf_transformation,[],[f23])).
% 15.24/2.29  fof(f23,axiom,(
% 15.24/2.29    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 15.24/2.29  fof(f214,plain,(
% 15.24/2.29    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl11_4),
% 15.24/2.29    inference(superposition,[],[f186,f114])).
% 15.24/2.29  fof(f186,plain,(
% 15.24/2.29    ( ! [X0] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))) ) | ~spl11_4),
% 15.24/2.29    inference(avatar_component_clause,[],[f185])).
% 15.24/2.29  fof(f185,plain,(
% 15.24/2.29    spl11_4 <=> ! [X0] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))),
% 15.24/2.29    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 15.24/2.29  fof(f15218,plain,(
% 15.24/2.29    ~r2_hidden(sK1,k2_relat_1(sK2)) | (spl11_2 | ~spl11_4)),
% 15.24/2.29    inference(resolution,[],[f15213,f135])).
% 15.24/2.29  fof(f135,plain,(
% 15.24/2.29    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 15.24/2.29    inference(equality_resolution,[],[f87])).
% 15.24/2.29  fof(f87,plain,(
% 15.24/2.29    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 15.24/2.29    inference(cnf_transformation,[],[f49])).
% 15.24/2.29  fof(f15213,plain,(
% 15.24/2.29    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK1),sK2)) ) | (spl11_2 | ~spl11_4)),
% 15.24/2.29    inference(subsumption_resolution,[],[f15212,f186])).
% 15.24/2.29  fof(f15212,plain,(
% 15.24/2.29    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK1),sK2) | ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ) | spl11_2),
% 15.24/2.29    inference(subsumption_resolution,[],[f15211,f149])).
% 15.24/2.29  fof(f149,plain,(
% 15.24/2.29    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | spl11_2),
% 15.24/2.29    inference(avatar_component_clause,[],[f147])).
% 15.24/2.29  fof(f15211,plain,(
% 15.24/2.29    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK1),sK2) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ) | spl11_2),
% 15.24/2.29    inference(superposition,[],[f90,f14264])).
% 15.24/2.29  fof(f14264,plain,(
% 15.24/2.29    sK1 = sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | spl11_2),
% 15.24/2.29    inference(subsumption_resolution,[],[f14263,f10902])).
% 15.24/2.29  fof(f10902,plain,(
% 15.24/2.29    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) )),
% 15.24/2.29    inference(superposition,[],[f130,f10576])).
% 15.24/2.29  fof(f130,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 15.24/2.29    inference(definition_unfolding,[],[f109,f112,f112])).
% 15.24/2.29  fof(f109,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 15.24/2.29    inference(cnf_transformation,[],[f63])).
% 15.24/2.29  fof(f63,plain,(
% 15.24/2.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 15.24/2.29    inference(flattening,[],[f62])).
% 15.24/2.29  fof(f62,plain,(
% 15.24/2.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 15.24/2.29    inference(nnf_transformation,[],[f19])).
% 15.24/2.29  fof(f19,axiom,(
% 15.24/2.29    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 15.24/2.29  fof(f14263,plain,(
% 15.24/2.29    sK1 = sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(k4_tarski(sK0,sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | spl11_2),
% 15.24/2.29    inference(subsumption_resolution,[],[f14237,f149])).
% 15.24/2.29  fof(f14237,plain,(
% 15.24/2.29    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | sK1 = sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(k4_tarski(sK0,sK5(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)),
% 15.24/2.29    inference(resolution,[],[f11268,f10909])).
% 15.24/2.29  fof(f10909,plain,(
% 15.24/2.29    ( ! [X8] : (~r2_hidden(X8,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(k4_tarski(sK0,X8),sK2)) )),
% 15.24/2.29    inference(superposition,[],[f139,f10576])).
% 15.24/2.29  fof(f139,plain,(
% 15.24/2.29    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | ~r2_hidden(X1,X3)) )),
% 15.24/2.29    inference(equality_resolution,[],[f126])).
% 15.24/2.29  fof(f126,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 15.24/2.29    inference(definition_unfolding,[],[f107,f112])).
% 15.24/2.29  fof(f107,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 15.24/2.29    inference(cnf_transformation,[],[f61])).
% 15.24/2.29  fof(f61,plain,(
% 15.24/2.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 15.24/2.29    inference(flattening,[],[f60])).
% 15.24/2.29  fof(f60,plain,(
% 15.24/2.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 15.24/2.29    inference(nnf_transformation,[],[f17])).
% 15.24/2.29  fof(f17,axiom,(
% 15.24/2.29    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 15.24/2.29  fof(f11268,plain,(
% 15.24/2.29    ( ! [X0] : (r2_hidden(sK5(sK2,X0),X0) | k2_relat_1(sK2) = X0 | sK1 = sK5(sK2,X0)) )),
% 15.24/2.29    inference(resolution,[],[f10902,f89])).
% 15.24/2.29  fof(f89,plain,(
% 15.24/2.29    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),X1)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f49])).
% 15.24/2.29  fof(f90,plain,(
% 15.24/2.29    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | k2_relat_1(X0) = X1 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f49])).
% 15.24/2.29  fof(f200,plain,(
% 15.24/2.29    ~spl11_3),
% 15.24/2.29    inference(avatar_contradiction_clause,[],[f199])).
% 15.24/2.29  fof(f199,plain,(
% 15.24/2.29    $false | ~spl11_3),
% 15.24/2.29    inference(subsumption_resolution,[],[f198,f197])).
% 15.24/2.29  fof(f197,plain,(
% 15.24/2.29    k1_xboole_0 != sK2 | ~spl11_3),
% 15.24/2.29    inference(backward_demodulation,[],[f174,f195])).
% 15.24/2.29  fof(f195,plain,(
% 15.24/2.29    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK2,X0)) ) | ~spl11_3),
% 15.24/2.29    inference(resolution,[],[f189,f96])).
% 15.24/2.29  fof(f96,plain,(
% 15.24/2.29    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 15.24/2.29    inference(cnf_transformation,[],[f56])).
% 15.24/2.29  fof(f56,plain,(
% 15.24/2.29    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.24/2.29    inference(nnf_transformation,[],[f7])).
% 15.24/2.29  fof(f7,axiom,(
% 15.24/2.29    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 15.24/2.29  fof(f189,plain,(
% 15.24/2.29    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl11_3),
% 15.24/2.29    inference(resolution,[],[f183,f83])).
% 15.24/2.29  fof(f83,plain,(
% 15.24/2.29    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f42])).
% 15.24/2.29  fof(f42,plain,(
% 15.24/2.29    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.24/2.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 15.24/2.29  fof(f41,plain,(
% 15.24/2.29    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 15.24/2.29    introduced(choice_axiom,[])).
% 15.24/2.29  fof(f40,plain,(
% 15.24/2.29    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.24/2.29    inference(rectify,[],[f39])).
% 15.24/2.29  fof(f39,plain,(
% 15.24/2.29    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.24/2.29    inference(nnf_transformation,[],[f32])).
% 15.24/2.29  fof(f32,plain,(
% 15.24/2.29    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.24/2.29    inference(ennf_transformation,[],[f2])).
% 15.24/2.29  fof(f2,axiom,(
% 15.24/2.29    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 15.24/2.29  fof(f183,plain,(
% 15.24/2.29    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl11_3),
% 15.24/2.29    inference(avatar_component_clause,[],[f182])).
% 15.24/2.29  fof(f182,plain,(
% 15.24/2.29    spl11_3 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 15.24/2.29    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 15.24/2.29  fof(f174,plain,(
% 15.24/2.29    sK2 != k4_xboole_0(sK2,sK2)),
% 15.24/2.29    inference(forward_demodulation,[],[f171,f151])).
% 15.24/2.29  fof(f151,plain,(
% 15.24/2.29    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 15.24/2.29    inference(superposition,[],[f114,f121])).
% 15.24/2.29  fof(f121,plain,(
% 15.24/2.29    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 15.24/2.29    inference(definition_unfolding,[],[f101,f73,f112,f73])).
% 15.24/2.29  fof(f101,plain,(
% 15.24/2.29    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 15.24/2.29    inference(cnf_transformation,[],[f20])).
% 15.24/2.29  fof(f171,plain,(
% 15.24/2.29    k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) != k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 15.24/2.29    inference(resolution,[],[f155,f141])).
% 15.24/2.29  fof(f141,plain,(
% 15.24/2.29    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 15.24/2.29    inference(equality_resolution,[],[f140])).
% 15.24/2.29  fof(f140,plain,(
% 15.24/2.29    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X0 != X2) )),
% 15.24/2.29    inference(equality_resolution,[],[f129])).
% 15.24/2.29  fof(f129,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | X0 != X2) )),
% 15.24/2.29    inference(definition_unfolding,[],[f110,f112,f112])).
% 15.24/2.29  fof(f110,plain,(
% 15.24/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) )),
% 15.24/2.29    inference(cnf_transformation,[],[f63])).
% 15.24/2.29  fof(f155,plain,(
% 15.24/2.29    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK1),X0) | k4_xboole_0(X0,sK2) != X0) )),
% 15.24/2.29    inference(superposition,[],[f119,f114])).
% 15.24/2.29  fof(f119,plain,(
% 15.24/2.29    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 15.24/2.29    inference(definition_unfolding,[],[f97,f112])).
% 15.24/2.29  fof(f97,plain,(
% 15.24/2.29    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 15.24/2.29    inference(cnf_transformation,[],[f57])).
% 15.24/2.29  fof(f57,plain,(
% 15.24/2.29    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 15.24/2.29    inference(nnf_transformation,[],[f21])).
% 15.24/2.29  fof(f21,axiom,(
% 15.24/2.29    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 15.24/2.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 15.24/2.29  fof(f198,plain,(
% 15.24/2.29    k1_xboole_0 = sK2 | ~spl11_3),
% 15.24/2.29    inference(backward_demodulation,[],[f194,f195])).
% 15.24/2.29  fof(f194,plain,(
% 15.24/2.29    ( ! [X5] : (sK2 = k4_xboole_0(sK2,k2_enumset1(X5,X5,X5,X5))) ) | ~spl11_3),
% 15.24/2.29    inference(resolution,[],[f183,f118])).
% 15.24/2.29  fof(f118,plain,(
% 15.24/2.29    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 15.24/2.29    inference(definition_unfolding,[],[f98,f112])).
% 15.24/2.29  fof(f98,plain,(
% 15.24/2.29    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 15.24/2.29    inference(cnf_transformation,[],[f57])).
% 15.24/2.29  fof(f187,plain,(
% 15.24/2.29    spl11_3 | spl11_4),
% 15.24/2.29    inference(avatar_split_clause,[],[f175,f185,f182])).
% 15.24/2.29  fof(f175,plain,(
% 15.24/2.29    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) | ~r2_hidden(X1,sK2)) )),
% 15.24/2.29    inference(resolution,[],[f157,f139])).
% 15.24/2.29  fof(f157,plain,(
% 15.24/2.29    ( ! [X6,X4,X5] : (~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X6,sK2)) | r2_hidden(X4,X6)) )),
% 15.24/2.29    inference(superposition,[],[f125,f114])).
% 15.24/2.29  fof(f150,plain,(
% 15.24/2.29    ~spl11_1 | ~spl11_2),
% 15.24/2.29    inference(avatar_split_clause,[],[f113,f147,f143])).
% 15.24/2.29  fof(f113,plain,(
% 15.24/2.29    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 15.24/2.29    inference(definition_unfolding,[],[f65,f112,f112])).
% 15.24/2.29  fof(f65,plain,(
% 15.24/2.29    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 15.24/2.29    inference(cnf_transformation,[],[f34])).
% 15.24/2.29  % SZS output end Proof for theBenchmark
% 15.24/2.29  % (27997)------------------------------
% 15.24/2.29  % (27997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.24/2.29  % (27997)Termination reason: Refutation
% 15.24/2.29  
% 15.24/2.29  % (27997)Memory used [KB]: 19957
% 15.24/2.29  % (27997)Time elapsed: 1.851 s
% 15.24/2.29  % (27997)------------------------------
% 15.24/2.29  % (27997)------------------------------
% 15.24/2.29  % (27986)Success in time 1.918 s
%------------------------------------------------------------------------------
