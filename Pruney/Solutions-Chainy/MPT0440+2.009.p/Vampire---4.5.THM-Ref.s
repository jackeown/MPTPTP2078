%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:58 EST 2020

% Result     : Theorem 6.95s
% Output     : Refutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 195 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  294 ( 835 expanded)
%              Number of equality atoms :  122 ( 368 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9979,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f9964])).

fof(f9964,plain,(
    k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(superposition,[],[f8153,f9916])).

fof(f9916,plain,(
    k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(resolution,[],[f9758,f63])).

fof(f63,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f9758,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f9686])).

fof(f9686,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f426,f9529])).

fof(f9529,plain,
    ( sK0 = sK6(sK2,k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f9524])).

fof(f9524,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | sK0 = sK6(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f9517,f336])).

fof(f336,plain,(
    ! [X2] :
      ( r2_hidden(sK6(sK2,X2),X2)
      | k1_relat_1(sK2) = X2
      | sK0 = sK6(sK2,X2) ) ),
    inference(resolution,[],[f327,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK0 = X0 ) ),
    inference(superposition,[],[f78,f35])).

fof(f35,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k1_tarski(sK1) != k2_relat_1(sK2)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k1_tarski(sK1) != k2_relat_1(sK2)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1)))
      | X0 = X2 ) ),
    inference(superposition,[],[f45,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f9517,plain,
    ( ~ r2_hidden(sK6(sK2,k1_tarski(sK0)),k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(factoring,[],[f426])).

fof(f426,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK6(sK2,X3),k1_tarski(sK0))
      | ~ r2_hidden(sK6(sK2,X3),X3)
      | k1_relat_1(sK2) = X3 ) ),
    inference(resolution,[],[f401,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f401,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK1),sK2)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f153,f35])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k1_tarski(k4_tarski(X0,X1)))
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(superposition,[],[f61,f55])).

fof(f61,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k1_tarski(X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f8153,plain,(
    k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f8138])).

fof(f8138,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(superposition,[],[f36,f8092])).

fof(f8092,plain,(
    k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(resolution,[],[f8085,f63])).

fof(f8085,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f8013])).

fof(f8013,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(superposition,[],[f408,f7969])).

fof(f7969,plain,
    ( sK1 = sK3(sK2,k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f7962])).

fof(f7962,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | sK1 = sK3(sK2,k1_tarski(sK1)) ),
    inference(resolution,[],[f7956,f365])).

fof(f365,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK2,X1),X1)
      | k2_relat_1(sK2) = X1
      | sK1 = sK3(sK2,X1) ) ),
    inference(resolution,[],[f350,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f350,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK1 = X1 ) ),
    inference(superposition,[],[f84,f35])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X1 = X3 ) ),
    inference(forward_demodulation,[],[f81,f55])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 = X3 ) ),
    inference(resolution,[],[f46,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7956,plain,
    ( ~ r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(factoring,[],[f408])).

fof(f408,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3(sK2,X3),k1_tarski(sK1))
      | ~ r2_hidden(sK3(sK2,X3),X3)
      | k2_relat_1(sK2) = X3 ) ),
    inference(resolution,[],[f385,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f385,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK0,X0),sK2)
      | ~ r2_hidden(X0,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f143,f35])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X2),k1_tarski(k4_tarski(X0,X1)))
      | ~ r2_hidden(X2,k1_tarski(X1)) ) ),
    inference(superposition,[],[f60,f55])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (15637)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (15663)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (15636)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (15649)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (15646)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (15650)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (15643)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (15638)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (15639)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (15656)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (15669)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (15670)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (15642)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (15670)Refutation not found, incomplete strategy% (15670)------------------------------
% 0.20/0.53  % (15670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15670)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15670)Memory used [KB]: 1663
% 0.20/0.53  % (15670)Time elapsed: 0.128 s
% 0.20/0.53  % (15670)------------------------------
% 0.20/0.53  % (15670)------------------------------
% 0.20/0.54  % (15640)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (15648)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (15661)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (15645)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (15662)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (15652)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (15655)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (15668)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (15655)Refutation not found, incomplete strategy% (15655)------------------------------
% 0.20/0.55  % (15655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15655)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15655)Memory used [KB]: 10618
% 0.20/0.55  % (15655)Time elapsed: 0.149 s
% 0.20/0.55  % (15655)------------------------------
% 0.20/0.55  % (15655)------------------------------
% 0.20/0.55  % (15653)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (15667)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (15660)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (15665)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (15659)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (15666)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.57  % (15664)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.57  % (15654)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.58  % (15644)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.23/0.71  % (15693)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.23/0.73  % (15694)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.26/0.81  % (15638)Time limit reached!
% 3.26/0.81  % (15638)------------------------------
% 3.26/0.81  % (15638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.81  % (15638)Termination reason: Time limit
% 3.26/0.81  % (15638)Termination phase: Saturation
% 3.26/0.81  
% 3.26/0.81  % (15638)Memory used [KB]: 6908
% 3.26/0.81  % (15638)Time elapsed: 0.400 s
% 3.26/0.81  % (15638)------------------------------
% 3.26/0.81  % (15638)------------------------------
% 3.26/0.82  % (15665)Time limit reached!
% 3.26/0.82  % (15665)------------------------------
% 3.26/0.82  % (15665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.82  % (15665)Termination reason: Time limit
% 3.26/0.82  % (15665)Termination phase: Saturation
% 3.26/0.82  
% 3.26/0.82  % (15665)Memory used [KB]: 13560
% 3.26/0.82  % (15665)Time elapsed: 0.422 s
% 3.26/0.82  % (15665)------------------------------
% 3.26/0.82  % (15665)------------------------------
% 3.61/0.90  % (15653)Time limit reached!
% 3.61/0.90  % (15653)------------------------------
% 3.61/0.90  % (15653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.90  % (15653)Termination reason: Time limit
% 3.61/0.90  % (15653)Termination phase: Saturation
% 3.61/0.90  
% 3.61/0.90  % (15653)Memory used [KB]: 4989
% 3.61/0.90  % (15653)Time elapsed: 0.501 s
% 3.61/0.90  % (15653)------------------------------
% 3.61/0.90  % (15653)------------------------------
% 3.61/0.93  % (15643)Time limit reached!
% 3.61/0.93  % (15643)------------------------------
% 3.61/0.93  % (15643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.93  % (15643)Termination reason: Time limit
% 3.61/0.93  
% 3.61/0.93  % (15643)Memory used [KB]: 14967
% 3.61/0.93  % (15643)Time elapsed: 0.518 s
% 3.61/0.93  % (15643)------------------------------
% 3.61/0.93  % (15643)------------------------------
% 4.30/0.94  % (15695)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.30/0.96  % (15696)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.66/1.03  % (15697)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.97/1.07  % (15698)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.97/1.11  % (15644)Time limit reached!
% 4.97/1.11  % (15644)------------------------------
% 4.97/1.11  % (15644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.11  % (15644)Termination reason: Time limit
% 4.97/1.11  % (15644)Termination phase: Saturation
% 4.97/1.11  
% 4.97/1.11  % (15644)Memory used [KB]: 5884
% 4.97/1.11  % (15644)Time elapsed: 0.622 s
% 4.97/1.11  % (15644)------------------------------
% 4.97/1.11  % (15644)------------------------------
% 5.90/1.23  % (15637)Time limit reached!
% 5.90/1.23  % (15637)------------------------------
% 5.90/1.23  % (15637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.90/1.24  % (15699)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.90/1.24  % (15637)Termination reason: Time limit
% 5.90/1.24  
% 5.90/1.24  % (15637)Memory used [KB]: 9978
% 5.90/1.24  % (15637)Time elapsed: 0.818 s
% 5.90/1.24  % (15637)------------------------------
% 5.90/1.24  % (15637)------------------------------
% 6.95/1.31  % (15639)Time limit reached!
% 6.95/1.31  % (15639)------------------------------
% 6.95/1.31  % (15639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.95/1.31  % (15639)Termination reason: Time limit
% 6.95/1.31  % (15639)Termination phase: Saturation
% 6.95/1.31  
% 6.95/1.31  % (15639)Memory used [KB]: 7036
% 6.95/1.31  % (15639)Time elapsed: 0.900 s
% 6.95/1.31  % (15639)------------------------------
% 6.95/1.31  % (15639)------------------------------
% 6.95/1.31  % (15642)Refutation found. Thanks to Tanya!
% 6.95/1.31  % SZS status Theorem for theBenchmark
% 6.95/1.31  % SZS output start Proof for theBenchmark
% 6.95/1.31  fof(f9979,plain,(
% 6.95/1.31    $false),
% 6.95/1.31    inference(trivial_inequality_removal,[],[f9964])).
% 6.95/1.31  fof(f9964,plain,(
% 6.95/1.31    k1_tarski(sK0) != k1_tarski(sK0)),
% 6.95/1.31    inference(superposition,[],[f8153,f9916])).
% 6.95/1.31  fof(f9916,plain,(
% 6.95/1.31    k1_tarski(sK0) = k1_relat_1(sK2)),
% 6.95/1.31    inference(resolution,[],[f9758,f63])).
% 6.95/1.31  fof(f63,plain,(
% 6.95/1.31    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 6.95/1.31    inference(equality_resolution,[],[f62])).
% 6.95/1.31  fof(f62,plain,(
% 6.95/1.31    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 6.95/1.31    inference(equality_resolution,[],[f52])).
% 6.95/1.31  fof(f52,plain,(
% 6.95/1.31    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 6.95/1.31    inference(cnf_transformation,[],[f33])).
% 6.95/1.31  fof(f33,plain,(
% 6.95/1.31    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.95/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f31,f32])).
% 6.95/1.31  fof(f32,plain,(
% 6.95/1.31    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 6.95/1.31    introduced(choice_axiom,[])).
% 6.95/1.31  fof(f31,plain,(
% 6.95/1.31    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.95/1.31    inference(rectify,[],[f30])).
% 6.95/1.31  fof(f30,plain,(
% 6.95/1.31    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.95/1.31    inference(nnf_transformation,[],[f1])).
% 6.95/1.31  fof(f1,axiom,(
% 6.95/1.31    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.95/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 6.95/1.31  fof(f9758,plain,(
% 6.95/1.31    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 6.95/1.31    inference(duplicate_literal_removal,[],[f9686])).
% 6.95/1.31  fof(f9686,plain,(
% 6.95/1.31    ~r2_hidden(sK0,k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 6.95/1.31    inference(superposition,[],[f426,f9529])).
% 6.95/1.31  fof(f9529,plain,(
% 6.95/1.31    sK0 = sK6(sK2,k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 6.95/1.31    inference(duplicate_literal_removal,[],[f9524])).
% 6.95/1.31  fof(f9524,plain,(
% 6.95/1.31    k1_tarski(sK0) = k1_relat_1(sK2) | k1_tarski(sK0) = k1_relat_1(sK2) | sK0 = sK6(sK2,k1_tarski(sK0))),
% 6.95/1.31    inference(resolution,[],[f9517,f336])).
% 6.95/1.31  fof(f336,plain,(
% 6.95/1.31    ( ! [X2] : (r2_hidden(sK6(sK2,X2),X2) | k1_relat_1(sK2) = X2 | sK0 = sK6(sK2,X2)) )),
% 6.95/1.31    inference(resolution,[],[f327,f43])).
% 6.95/1.31  fof(f43,plain,(
% 6.95/1.31    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 6.95/1.31    inference(cnf_transformation,[],[f25])).
% 6.95/1.31  fof(f25,plain,(
% 6.95/1.31    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 6.95/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f24,f23,f22])).
% 6.95/1.31  fof(f22,plain,(
% 6.95/1.31    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 6.95/1.31    introduced(choice_axiom,[])).
% 6.95/1.31  fof(f23,plain,(
% 6.95/1.31    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 6.95/1.31    introduced(choice_axiom,[])).
% 6.95/1.31  fof(f24,plain,(
% 6.95/1.31    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 6.95/1.31    introduced(choice_axiom,[])).
% 6.95/1.31  fof(f21,plain,(
% 6.95/1.31    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 6.95/1.31    inference(rectify,[],[f20])).
% 6.95/1.31  fof(f20,plain,(
% 6.95/1.31    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 6.95/1.31    inference(nnf_transformation,[],[f6])).
% 6.95/1.31  fof(f6,axiom,(
% 6.95/1.31    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 6.95/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 6.95/1.31  fof(f327,plain,(
% 6.95/1.31    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) )),
% 6.95/1.31    inference(superposition,[],[f78,f35])).
% 6.95/1.31  fof(f35,plain,(
% 6.95/1.31    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 6.95/1.31    inference(cnf_transformation,[],[f13])).
% 6.95/1.31  fof(f13,plain,(
% 6.95/1.31    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 6.95/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 6.95/1.31  fof(f12,plain,(
% 6.95/1.31    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 6.95/1.31    introduced(choice_axiom,[])).
% 6.95/1.31  fof(f11,plain,(
% 6.95/1.31    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 6.95/1.31    inference(flattening,[],[f10])).
% 6.95/1.31  fof(f10,plain,(
% 6.95/1.31    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 6.95/1.31    inference(ennf_transformation,[],[f9])).
% 6.95/1.31  fof(f9,negated_conjecture,(
% 6.95/1.31    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 6.95/1.31    inference(negated_conjecture,[],[f8])).
% 6.95/1.31  fof(f8,conjecture,(
% 6.95/1.31    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 6.95/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 6.95/1.31  fof(f78,plain,(
% 6.95/1.31    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1))) | X0 = X2) )),
% 6.95/1.31    inference(superposition,[],[f45,f55])).
% 6.95/1.31  fof(f55,plain,(
% 6.95/1.31    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 6.95/1.31    inference(cnf_transformation,[],[f5])).
% 6.95/1.31  fof(f5,axiom,(
% 6.95/1.31    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 6.95/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 6.95/1.31  fof(f45,plain,(
% 6.95/1.31    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | X0 = X2) )),
% 6.95/1.31    inference(cnf_transformation,[],[f27])).
% 6.95/1.31  fof(f27,plain,(
% 6.95/1.31    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 6.95/1.31    inference(flattening,[],[f26])).
% 6.95/1.31  fof(f26,plain,(
% 6.95/1.31    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 6.95/1.31    inference(nnf_transformation,[],[f3])).
% 6.95/1.31  fof(f3,axiom,(
% 6.95/1.31    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 6.95/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 6.95/1.31  fof(f9517,plain,(
% 6.95/1.31    ~r2_hidden(sK6(sK2,k1_tarski(sK0)),k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 6.95/1.31    inference(factoring,[],[f426])).
% 6.95/1.31  fof(f426,plain,(
% 6.95/1.31    ( ! [X3] : (~r2_hidden(sK6(sK2,X3),k1_tarski(sK0)) | ~r2_hidden(sK6(sK2,X3),X3) | k1_relat_1(sK2) = X3) )),
% 6.95/1.31    inference(resolution,[],[f401,f44])).
% 6.95/1.31  fof(f44,plain,(
% 6.95/1.31    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 6.95/1.31    inference(cnf_transformation,[],[f25])).
% 6.95/1.31  fof(f401,plain,(
% 6.95/1.31    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK1),sK2) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 6.95/1.31    inference(superposition,[],[f153,f35])).
% 6.95/1.31  fof(f153,plain,(
% 6.95/1.31    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),k1_tarski(k4_tarski(X0,X1))) | ~r2_hidden(X2,k1_tarski(X0))) )),
% 6.95/1.31    inference(superposition,[],[f61,f55])).
% 6.95/1.31  fof(f61,plain,(
% 6.95/1.31    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k1_tarski(X3))) | ~r2_hidden(X0,X2)) )),
% 6.95/1.31    inference(equality_resolution,[],[f50])).
% 6.95/1.31  fof(f50,plain,(
% 6.95/1.31    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 6.95/1.31    inference(cnf_transformation,[],[f29])).
% 6.95/1.31  fof(f29,plain,(
% 6.95/1.31    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 6.95/1.31    inference(flattening,[],[f28])).
% 6.95/1.31  fof(f28,plain,(
% 6.95/1.31    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 6.95/1.31    inference(nnf_transformation,[],[f4])).
% 6.95/1.31  fof(f4,axiom,(
% 6.95/1.31    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 6.95/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 6.95/1.31  fof(f8153,plain,(
% 6.95/1.31    k1_tarski(sK0) != k1_relat_1(sK2)),
% 6.95/1.31    inference(trivial_inequality_removal,[],[f8138])).
% 6.95/1.31  fof(f8138,plain,(
% 6.95/1.31    k1_tarski(sK1) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 6.95/1.31    inference(superposition,[],[f36,f8092])).
% 6.95/1.31  fof(f8092,plain,(
% 6.95/1.31    k1_tarski(sK1) = k2_relat_1(sK2)),
% 6.95/1.31    inference(resolution,[],[f8085,f63])).
% 6.95/1.31  fof(f8085,plain,(
% 6.95/1.31    ~r2_hidden(sK1,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2)),
% 6.95/1.31    inference(duplicate_literal_removal,[],[f8013])).
% 6.95/1.31  fof(f8013,plain,(
% 6.95/1.31    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2) | k1_tarski(sK1) = k2_relat_1(sK2)),
% 6.95/1.31    inference(superposition,[],[f408,f7969])).
% 6.95/1.31  fof(f7969,plain,(
% 6.95/1.31    sK1 = sK3(sK2,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2)),
% 6.95/1.31    inference(duplicate_literal_removal,[],[f7962])).
% 6.95/1.31  fof(f7962,plain,(
% 6.95/1.31    k1_tarski(sK1) = k2_relat_1(sK2) | k1_tarski(sK1) = k2_relat_1(sK2) | sK1 = sK3(sK2,k1_tarski(sK1))),
% 6.95/1.31    inference(resolution,[],[f7956,f365])).
% 6.95/1.31  fof(f365,plain,(
% 6.95/1.31    ( ! [X1] : (r2_hidden(sK3(sK2,X1),X1) | k2_relat_1(sK2) = X1 | sK1 = sK3(sK2,X1)) )),
% 6.95/1.31    inference(resolution,[],[f350,f39])).
% 6.95/1.31  fof(f39,plain,(
% 6.95/1.31    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 6.95/1.31    inference(cnf_transformation,[],[f19])).
% 6.95/1.31  fof(f19,plain,(
% 6.95/1.31    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.95/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 6.95/1.31  fof(f16,plain,(
% 6.95/1.31    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 6.95/1.31    introduced(choice_axiom,[])).
% 6.95/1.31  fof(f17,plain,(
% 6.95/1.31    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 6.95/1.31    introduced(choice_axiom,[])).
% 6.95/1.31  fof(f18,plain,(
% 6.95/1.31    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 6.95/1.31    introduced(choice_axiom,[])).
% 6.95/1.31  fof(f15,plain,(
% 6.95/1.31    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.95/1.31    inference(rectify,[],[f14])).
% 6.95/1.31  fof(f14,plain,(
% 6.95/1.31    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 6.95/1.31    inference(nnf_transformation,[],[f7])).
% 6.95/1.31  fof(f7,axiom,(
% 6.95/1.31    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 6.95/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 6.95/1.31  fof(f350,plain,(
% 6.95/1.31    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) )),
% 6.95/1.31    inference(superposition,[],[f84,f35])).
% 6.95/1.31  fof(f84,plain,(
% 6.95/1.31    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X1 = X3) )),
% 6.95/1.31    inference(forward_demodulation,[],[f81,f55])).
% 6.95/1.31  fof(f81,plain,(
% 6.95/1.31    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 = X3) )),
% 6.95/1.31    inference(resolution,[],[f46,f64])).
% 6.95/1.31  fof(f64,plain,(
% 6.95/1.31    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 6.95/1.31    inference(equality_resolution,[],[f51])).
% 6.95/1.31  fof(f51,plain,(
% 6.95/1.31    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.95/1.31    inference(cnf_transformation,[],[f33])).
% 6.95/1.31  fof(f46,plain,(
% 6.95/1.31    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 6.95/1.31    inference(cnf_transformation,[],[f27])).
% 6.95/1.31  fof(f7956,plain,(
% 6.95/1.31    ~r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2)),
% 6.95/1.31    inference(factoring,[],[f408])).
% 6.95/1.31  fof(f408,plain,(
% 6.95/1.31    ( ! [X3] : (~r2_hidden(sK3(sK2,X3),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,X3),X3) | k2_relat_1(sK2) = X3) )),
% 6.95/1.31    inference(resolution,[],[f385,f40])).
% 6.95/1.31  fof(f40,plain,(
% 6.95/1.31    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 6.95/1.31    inference(cnf_transformation,[],[f19])).
% 6.95/1.31  fof(f385,plain,(
% 6.95/1.31    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK2) | ~r2_hidden(X0,k1_tarski(sK1))) )),
% 6.95/1.31    inference(superposition,[],[f143,f35])).
% 6.95/1.31  fof(f143,plain,(
% 6.95/1.31    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X2),k1_tarski(k4_tarski(X0,X1))) | ~r2_hidden(X2,k1_tarski(X1))) )),
% 6.95/1.31    inference(superposition,[],[f60,f55])).
% 6.95/1.31  fof(f60,plain,(
% 6.95/1.31    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3)) )),
% 6.95/1.31    inference(equality_resolution,[],[f47])).
% 6.95/1.31  fof(f47,plain,(
% 6.95/1.31    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 6.95/1.31    inference(cnf_transformation,[],[f27])).
% 6.95/1.31  fof(f36,plain,(
% 6.95/1.31    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 6.95/1.31    inference(cnf_transformation,[],[f13])).
% 6.95/1.31  % SZS output end Proof for theBenchmark
% 6.95/1.31  % (15642)------------------------------
% 6.95/1.31  % (15642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.95/1.31  % (15642)Termination reason: Refutation
% 6.95/1.31  
% 6.95/1.31  % (15642)Memory used [KB]: 9083
% 6.95/1.31  % (15642)Time elapsed: 0.880 s
% 6.95/1.31  % (15642)------------------------------
% 6.95/1.31  % (15642)------------------------------
% 6.95/1.31  % (15635)Success in time 0.947 s
%------------------------------------------------------------------------------
