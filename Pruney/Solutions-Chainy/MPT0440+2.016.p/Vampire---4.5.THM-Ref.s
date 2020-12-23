%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:59 EST 2020

% Result     : Theorem 8.34s
% Output     : Refutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 205 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  272 ( 787 expanded)
%              Number of equality atoms :  109 ( 335 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12496,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f12470])).

fof(f12470,plain,(
    k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(superposition,[],[f10986,f12409])).

fof(f12409,plain,(
    k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(resolution,[],[f12261,f63])).

fof(f63,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X2,X3))) ),
    inference(backward_demodulation,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X0 != X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f12261,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK0,X0),k1_tarski(k4_tarski(sK0,X1)))
      | k1_tarski(sK0) = k1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f12259,f52])).

fof(f12259,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK0) = k1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(sK0,X0),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(X1))) ) ),
    inference(resolution,[],[f12210,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f12210,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f12114])).

fof(f12114,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f461,f12072])).

fof(f12072,plain,
    ( sK0 = sK6(sK2,k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f12069])).

fof(f12069,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | sK0 = sK6(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f12063,f385])).

fof(f385,plain,(
    ! [X2] :
      ( r2_hidden(sK6(sK2,X2),X2)
      | k1_relat_1(sK2) = X2
      | sK0 = sK6(sK2,X2) ) ),
    inference(resolution,[],[f353,f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f353,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK0 = X0 ) ),
    inference(superposition,[],[f71,f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1)))
      | X0 = X2 ) ),
    inference(superposition,[],[f46,f52])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f12063,plain,
    ( ~ r2_hidden(sK6(sK2,k1_tarski(sK0)),k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(factoring,[],[f461])).

fof(f461,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK6(sK2,X8),k1_tarski(sK0))
      | ~ r2_hidden(sK6(sK2,X8),X8)
      | k1_relat_1(sK2) = X8 ) ),
    inference(resolution,[],[f393,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f393,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK1),sK2)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f144,f33])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k1_tarski(k4_tarski(X0,X1)))
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(superposition,[],[f60,f52])).

fof(f60,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k1_tarski(X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10986,plain,(
    k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f10960])).

fof(f10960,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(superposition,[],[f34,f10904])).

fof(f10904,plain,(
    k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(resolution,[],[f10820,f63])).

fof(f10820,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1,X0),k1_tarski(k4_tarski(sK1,X1)))
      | k1_tarski(sK1) = k2_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f10818,f52])).

fof(f10818,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK1) = k2_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(sK1,X0),k2_zfmisc_1(k1_tarski(sK1),k1_tarski(X1))) ) ),
    inference(resolution,[],[f10772,f49])).

fof(f10772,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f10690])).

fof(f10690,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(superposition,[],[f446,f10646])).

fof(f10646,plain,
    ( sK1 = sK3(sK2,k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f10641])).

fof(f10641,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | sK1 = sK3(sK2,k1_tarski(sK1)) ),
    inference(resolution,[],[f10609,f406])).

fof(f406,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK2,X1),X1)
      | k2_relat_1(sK2) = X1
      | sK1 = sK3(sK2,X1) ) ),
    inference(resolution,[],[f369,f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f369,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK1 = X1 ) ),
    inference(superposition,[],[f94,f33])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1)))
      | X1 = X3 ) ),
    inference(superposition,[],[f50,f52])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10609,plain,
    ( ~ r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(factoring,[],[f446])).

fof(f446,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK3(sK2,X8),k1_tarski(sK1))
      | ~ r2_hidden(sK3(sK2,X8),X8)
      | k2_relat_1(sK2) = X8 ) ),
    inference(resolution,[],[f378,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f378,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK0,X0),sK2)
      | ~ r2_hidden(X0,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f132,f33])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X2),k1_tarski(k4_tarski(X0,X1)))
      | ~ r2_hidden(X2,k1_tarski(X1)) ) ),
    inference(superposition,[],[f59,f52])).

fof(f59,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (5145)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (5142)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5158)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (5137)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (5139)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (5136)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (5144)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (5146)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (5137)Refutation not found, incomplete strategy% (5137)------------------------------
% 0.21/0.52  % (5137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5137)Memory used [KB]: 1663
% 0.21/0.52  % (5137)Time elapsed: 0.120 s
% 0.21/0.52  % (5137)------------------------------
% 0.21/0.52  % (5137)------------------------------
% 0.21/0.53  % (5150)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (5153)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.53  % (5164)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.53  % (5141)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.53  % (5140)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.54  % (5159)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.54  % (5151)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.54  % (5138)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.33/0.54  % (5162)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.54  % (5155)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.54  % (5143)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.54  % (5163)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (5161)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.54  % (5166)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.54  % (5166)Refutation not found, incomplete strategy% (5166)------------------------------
% 1.33/0.54  % (5166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (5166)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (5166)Memory used [KB]: 1663
% 1.33/0.54  % (5166)Time elapsed: 0.002 s
% 1.33/0.54  % (5166)------------------------------
% 1.33/0.54  % (5166)------------------------------
% 1.33/0.54  % (5165)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.55  % (5157)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.55  % (5152)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.55  % (5149)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.55  % (5152)Refutation not found, incomplete strategy% (5152)------------------------------
% 1.46/0.55  % (5152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (5152)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (5152)Memory used [KB]: 10618
% 1.46/0.55  % (5152)Time elapsed: 0.132 s
% 1.46/0.55  % (5152)------------------------------
% 1.46/0.55  % (5152)------------------------------
% 1.46/0.55  % (5156)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.55  % (5148)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.56  % (5154)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.56  % (5147)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.01/0.64  % (5139)Refutation not found, incomplete strategy% (5139)------------------------------
% 2.01/0.64  % (5139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.65  % (5136)Refutation not found, incomplete strategy% (5136)------------------------------
% 2.01/0.65  % (5136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.65  % (5136)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.65  
% 2.01/0.65  % (5136)Memory used [KB]: 1663
% 2.01/0.65  % (5136)Time elapsed: 0.237 s
% 2.01/0.65  % (5136)------------------------------
% 2.01/0.65  % (5136)------------------------------
% 2.01/0.65  % (5139)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.65  
% 2.01/0.65  % (5139)Memory used [KB]: 6140
% 2.01/0.65  % (5139)Time elapsed: 0.235 s
% 2.01/0.65  % (5139)------------------------------
% 2.01/0.65  % (5139)------------------------------
% 2.43/0.68  % (5259)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.43/0.69  % (5264)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.43/0.71  % (5265)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.88/0.76  % (5290)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.01/0.79  % (5298)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.01/0.81  % (5138)Time limit reached!
% 3.01/0.81  % (5138)------------------------------
% 3.01/0.81  % (5138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.83  % (5138)Termination reason: Time limit
% 3.32/0.83  
% 3.32/0.83  % (5138)Memory used [KB]: 7803
% 3.32/0.83  % (5138)Time elapsed: 0.408 s
% 3.32/0.83  % (5138)------------------------------
% 3.32/0.83  % (5138)------------------------------
% 3.51/0.86  % (5161)Time limit reached!
% 3.51/0.86  % (5161)------------------------------
% 3.51/0.86  % (5161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.86  % (5161)Termination reason: Time limit
% 3.51/0.86  
% 3.51/0.86  % (5161)Memory used [KB]: 15223
% 3.51/0.86  % (5161)Time elapsed: 0.431 s
% 3.51/0.86  % (5161)------------------------------
% 3.51/0.86  % (5161)------------------------------
% 3.51/0.90  % (5150)Time limit reached!
% 3.51/0.90  % (5150)------------------------------
% 3.51/0.90  % (5150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.90  % (5150)Termination reason: Time limit
% 3.51/0.90  % (5150)Termination phase: Saturation
% 3.51/0.90  
% 3.51/0.90  % (5150)Memory used [KB]: 5628
% 3.51/0.90  % (5150)Time elapsed: 0.500 s
% 3.51/0.90  % (5150)------------------------------
% 3.51/0.90  % (5150)------------------------------
% 3.51/0.92  % (5142)Time limit reached!
% 3.51/0.92  % (5142)------------------------------
% 3.51/0.92  % (5142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.92  % (5142)Termination reason: Time limit
% 3.51/0.92  
% 3.51/0.92  % (5142)Memory used [KB]: 15479
% 3.51/0.92  % (5142)Time elapsed: 0.515 s
% 3.51/0.92  % (5142)------------------------------
% 3.51/0.92  % (5142)------------------------------
% 4.00/0.93  % (5341)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.26/0.99  % (5342)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.26/1.03  % (5343)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.68/1.05  % (5344)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.57/1.10  % (5143)Time limit reached!
% 5.57/1.10  % (5143)------------------------------
% 5.57/1.10  % (5143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.57/1.10  % (5143)Termination reason: Time limit
% 5.57/1.10  
% 5.57/1.10  % (5143)Memory used [KB]: 7419
% 5.57/1.10  % (5143)Time elapsed: 0.626 s
% 5.57/1.10  % (5143)------------------------------
% 5.57/1.10  % (5143)------------------------------
% 6.21/1.22  % (5346)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 7.87/1.40  % (5265)Time limit reached!
% 7.87/1.40  % (5265)------------------------------
% 7.87/1.40  % (5265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.87/1.40  % (5265)Termination reason: Time limit
% 7.87/1.40  
% 7.87/1.40  % (5265)Memory used [KB]: 15351
% 7.87/1.40  % (5265)Time elapsed: 0.811 s
% 7.87/1.40  % (5265)------------------------------
% 7.87/1.40  % (5265)------------------------------
% 7.87/1.41  % (5148)Time limit reached!
% 7.87/1.41  % (5148)------------------------------
% 7.87/1.41  % (5148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.87/1.43  % (5148)Termination reason: Time limit
% 7.87/1.43  % (5148)Termination phase: Saturation
% 7.87/1.43  
% 7.87/1.43  % (5148)Memory used [KB]: 14967
% 7.87/1.43  % (5148)Time elapsed: 1.011 s
% 7.87/1.43  % (5148)------------------------------
% 7.87/1.43  % (5148)------------------------------
% 7.87/1.43  % (5164)Time limit reached!
% 7.87/1.43  % (5164)------------------------------
% 7.87/1.43  % (5164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.87/1.43  % (5164)Termination reason: Time limit
% 7.87/1.43  
% 7.87/1.43  % (5164)Memory used [KB]: 16758
% 7.87/1.43  % (5164)Time elapsed: 1.017 s
% 7.87/1.43  % (5164)------------------------------
% 7.87/1.43  % (5164)------------------------------
% 8.34/1.45  % (5141)Refutation found. Thanks to Tanya!
% 8.34/1.45  % SZS status Theorem for theBenchmark
% 8.34/1.45  % SZS output start Proof for theBenchmark
% 8.34/1.45  fof(f12496,plain,(
% 8.34/1.45    $false),
% 8.34/1.45    inference(trivial_inequality_removal,[],[f12470])).
% 8.34/1.45  fof(f12470,plain,(
% 8.34/1.45    k1_tarski(sK0) != k1_tarski(sK0)),
% 8.34/1.45    inference(superposition,[],[f10986,f12409])).
% 8.34/1.45  fof(f12409,plain,(
% 8.34/1.45    k1_tarski(sK0) = k1_relat_1(sK2)),
% 8.34/1.45    inference(resolution,[],[f12261,f63])).
% 8.34/1.45  fof(f63,plain,(
% 8.34/1.45    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X2,X3)))) )),
% 8.34/1.45    inference(backward_demodulation,[],[f58,f52])).
% 8.34/1.45  fof(f52,plain,(
% 8.34/1.45    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 8.34/1.45    inference(cnf_transformation,[],[f5])).
% 8.34/1.45  fof(f5,axiom,(
% 8.34/1.45    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 8.34/1.45  fof(f58,plain,(
% 8.34/1.45    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 8.34/1.45    inference(equality_resolution,[],[f57])).
% 8.34/1.45  fof(f57,plain,(
% 8.34/1.45    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X0 != X2) )),
% 8.34/1.45    inference(equality_resolution,[],[f45])).
% 8.34/1.45  fof(f45,plain,(
% 8.34/1.45    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) )),
% 8.34/1.45    inference(cnf_transformation,[],[f27])).
% 8.34/1.45  fof(f27,plain,(
% 8.34/1.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 8.34/1.45    inference(flattening,[],[f26])).
% 8.34/1.45  fof(f26,plain,(
% 8.34/1.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 8.34/1.45    inference(nnf_transformation,[],[f4])).
% 8.34/1.45  fof(f4,axiom,(
% 8.34/1.45    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 8.34/1.45  fof(f12261,plain,(
% 8.34/1.45    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK0,X0),k1_tarski(k4_tarski(sK0,X1))) | k1_tarski(sK0) = k1_relat_1(sK2)) )),
% 8.34/1.45    inference(forward_demodulation,[],[f12259,f52])).
% 8.34/1.45  fof(f12259,plain,(
% 8.34/1.45    ( ! [X0,X1] : (k1_tarski(sK0) = k1_relat_1(sK2) | ~r2_hidden(k4_tarski(sK0,X0),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(X1)))) )),
% 8.34/1.45    inference(resolution,[],[f12210,f49])).
% 8.34/1.45  fof(f49,plain,(
% 8.34/1.45    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 8.34/1.45    inference(cnf_transformation,[],[f31])).
% 8.34/1.45  fof(f31,plain,(
% 8.34/1.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 8.34/1.45    inference(flattening,[],[f30])).
% 8.34/1.45  fof(f30,plain,(
% 8.34/1.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 8.34/1.45    inference(nnf_transformation,[],[f3])).
% 8.34/1.45  fof(f3,axiom,(
% 8.34/1.45    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 8.34/1.45  fof(f12210,plain,(
% 8.34/1.45    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 8.34/1.45    inference(duplicate_literal_removal,[],[f12114])).
% 8.34/1.45  fof(f12114,plain,(
% 8.34/1.45    ~r2_hidden(sK0,k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 8.34/1.45    inference(superposition,[],[f461,f12072])).
% 8.34/1.45  fof(f12072,plain,(
% 8.34/1.45    sK0 = sK6(sK2,k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 8.34/1.45    inference(duplicate_literal_removal,[],[f12069])).
% 8.34/1.45  fof(f12069,plain,(
% 8.34/1.45    k1_tarski(sK0) = k1_relat_1(sK2) | k1_tarski(sK0) = k1_relat_1(sK2) | sK0 = sK6(sK2,k1_tarski(sK0))),
% 8.34/1.45    inference(resolution,[],[f12063,f385])).
% 8.34/1.45  fof(f385,plain,(
% 8.34/1.45    ( ! [X2] : (r2_hidden(sK6(sK2,X2),X2) | k1_relat_1(sK2) = X2 | sK0 = sK6(sK2,X2)) )),
% 8.34/1.45    inference(resolution,[],[f353,f41])).
% 8.34/1.45  fof(f41,plain,(
% 8.34/1.45    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 8.34/1.45    inference(cnf_transformation,[],[f25])).
% 8.34/1.45  fof(f25,plain,(
% 8.34/1.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 8.34/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f24,f23,f22])).
% 8.34/1.45  fof(f22,plain,(
% 8.34/1.45    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 8.34/1.45    introduced(choice_axiom,[])).
% 8.34/1.45  fof(f23,plain,(
% 8.34/1.45    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 8.34/1.45    introduced(choice_axiom,[])).
% 8.34/1.45  fof(f24,plain,(
% 8.34/1.45    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 8.34/1.45    introduced(choice_axiom,[])).
% 8.34/1.45  fof(f21,plain,(
% 8.34/1.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 8.34/1.45    inference(rectify,[],[f20])).
% 8.34/1.45  fof(f20,plain,(
% 8.34/1.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 8.34/1.45    inference(nnf_transformation,[],[f6])).
% 8.34/1.45  fof(f6,axiom,(
% 8.34/1.45    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 8.34/1.45  fof(f353,plain,(
% 8.34/1.45    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) )),
% 8.34/1.45    inference(superposition,[],[f71,f33])).
% 8.34/1.45  fof(f33,plain,(
% 8.34/1.45    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 8.34/1.45    inference(cnf_transformation,[],[f13])).
% 8.34/1.45  fof(f13,plain,(
% 8.34/1.45    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 8.34/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 8.34/1.45  fof(f12,plain,(
% 8.34/1.45    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 8.34/1.45    introduced(choice_axiom,[])).
% 8.34/1.45  fof(f11,plain,(
% 8.34/1.45    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 8.34/1.45    inference(flattening,[],[f10])).
% 8.34/1.45  fof(f10,plain,(
% 8.34/1.45    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 8.34/1.45    inference(ennf_transformation,[],[f9])).
% 8.34/1.45  fof(f9,negated_conjecture,(
% 8.34/1.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 8.34/1.45    inference(negated_conjecture,[],[f8])).
% 8.34/1.45  fof(f8,conjecture,(
% 8.34/1.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 8.34/1.45  fof(f71,plain,(
% 8.34/1.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1))) | X0 = X2) )),
% 8.34/1.45    inference(superposition,[],[f46,f52])).
% 8.34/1.45  fof(f46,plain,(
% 8.34/1.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | X0 = X2) )),
% 8.34/1.45    inference(cnf_transformation,[],[f29])).
% 8.34/1.45  fof(f29,plain,(
% 8.34/1.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 8.34/1.45    inference(flattening,[],[f28])).
% 8.34/1.45  fof(f28,plain,(
% 8.34/1.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 8.34/1.45    inference(nnf_transformation,[],[f2])).
% 8.55/1.47  fof(f2,axiom,(
% 8.55/1.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 8.55/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 8.55/1.47  fof(f12063,plain,(
% 8.55/1.47    ~r2_hidden(sK6(sK2,k1_tarski(sK0)),k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 8.55/1.47    inference(factoring,[],[f461])).
% 8.55/1.47  fof(f461,plain,(
% 8.55/1.47    ( ! [X8] : (~r2_hidden(sK6(sK2,X8),k1_tarski(sK0)) | ~r2_hidden(sK6(sK2,X8),X8) | k1_relat_1(sK2) = X8) )),
% 8.55/1.47    inference(resolution,[],[f393,f42])).
% 8.55/1.47  fof(f42,plain,(
% 8.55/1.47    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 8.55/1.47    inference(cnf_transformation,[],[f25])).
% 8.55/1.47  fof(f393,plain,(
% 8.55/1.47    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK1),sK2) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 8.55/1.47    inference(superposition,[],[f144,f33])).
% 8.55/1.47  fof(f144,plain,(
% 8.55/1.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),k1_tarski(k4_tarski(X0,X1))) | ~r2_hidden(X2,k1_tarski(X0))) )),
% 8.55/1.47    inference(superposition,[],[f60,f52])).
% 8.55/1.47  fof(f60,plain,(
% 8.55/1.47    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k1_tarski(X3))) | ~r2_hidden(X0,X2)) )),
% 8.55/1.47    inference(equality_resolution,[],[f51])).
% 8.55/1.47  fof(f51,plain,(
% 8.55/1.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 8.55/1.47    inference(cnf_transformation,[],[f31])).
% 8.55/1.47  fof(f10986,plain,(
% 8.55/1.47    k1_tarski(sK0) != k1_relat_1(sK2)),
% 8.55/1.47    inference(trivial_inequality_removal,[],[f10960])).
% 8.55/1.47  fof(f10960,plain,(
% 8.55/1.47    k1_tarski(sK1) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 8.55/1.47    inference(superposition,[],[f34,f10904])).
% 8.55/1.47  fof(f10904,plain,(
% 8.55/1.47    k1_tarski(sK1) = k2_relat_1(sK2)),
% 8.55/1.47    inference(resolution,[],[f10820,f63])).
% 8.55/1.47  fof(f10820,plain,(
% 8.55/1.47    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1,X0),k1_tarski(k4_tarski(sK1,X1))) | k1_tarski(sK1) = k2_relat_1(sK2)) )),
% 8.55/1.47    inference(forward_demodulation,[],[f10818,f52])).
% 8.55/1.47  fof(f10818,plain,(
% 8.55/1.47    ( ! [X0,X1] : (k1_tarski(sK1) = k2_relat_1(sK2) | ~r2_hidden(k4_tarski(sK1,X0),k2_zfmisc_1(k1_tarski(sK1),k1_tarski(X1)))) )),
% 8.55/1.47    inference(resolution,[],[f10772,f49])).
% 8.55/1.47  fof(f10772,plain,(
% 8.55/1.47    ~r2_hidden(sK1,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2)),
% 8.55/1.47    inference(duplicate_literal_removal,[],[f10690])).
% 8.55/1.47  fof(f10690,plain,(
% 8.55/1.47    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2) | k1_tarski(sK1) = k2_relat_1(sK2)),
% 8.55/1.47    inference(superposition,[],[f446,f10646])).
% 8.55/1.47  fof(f10646,plain,(
% 8.55/1.47    sK1 = sK3(sK2,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2)),
% 8.55/1.47    inference(duplicate_literal_removal,[],[f10641])).
% 8.55/1.47  fof(f10641,plain,(
% 8.55/1.47    k1_tarski(sK1) = k2_relat_1(sK2) | k1_tarski(sK1) = k2_relat_1(sK2) | sK1 = sK3(sK2,k1_tarski(sK1))),
% 8.55/1.47    inference(resolution,[],[f10609,f406])).
% 8.55/1.47  fof(f406,plain,(
% 8.55/1.47    ( ! [X1] : (r2_hidden(sK3(sK2,X1),X1) | k2_relat_1(sK2) = X1 | sK1 = sK3(sK2,X1)) )),
% 8.55/1.47    inference(resolution,[],[f369,f37])).
% 8.55/1.47  fof(f37,plain,(
% 8.55/1.47    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 8.55/1.47    inference(cnf_transformation,[],[f19])).
% 8.55/1.47  fof(f19,plain,(
% 8.55/1.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 8.55/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 8.55/1.47  fof(f16,plain,(
% 8.55/1.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 8.55/1.47    introduced(choice_axiom,[])).
% 8.55/1.47  fof(f17,plain,(
% 8.55/1.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 8.55/1.47    introduced(choice_axiom,[])).
% 8.55/1.47  fof(f18,plain,(
% 8.55/1.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 8.55/1.47    introduced(choice_axiom,[])).
% 8.55/1.47  fof(f15,plain,(
% 8.55/1.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 8.55/1.47    inference(rectify,[],[f14])).
% 8.55/1.47  fof(f14,plain,(
% 8.55/1.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 8.55/1.47    inference(nnf_transformation,[],[f7])).
% 8.55/1.47  fof(f7,axiom,(
% 8.55/1.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 8.55/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 8.55/1.47  fof(f369,plain,(
% 8.55/1.47    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) )),
% 8.55/1.47    inference(superposition,[],[f94,f33])).
% 8.55/1.47  fof(f94,plain,(
% 8.55/1.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1))) | X1 = X3) )),
% 8.55/1.47    inference(superposition,[],[f50,f52])).
% 8.55/1.47  fof(f50,plain,(
% 8.55/1.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 = X3) )),
% 8.55/1.47    inference(cnf_transformation,[],[f31])).
% 8.55/1.47  fof(f10609,plain,(
% 8.55/1.47    ~r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2)),
% 8.55/1.47    inference(factoring,[],[f446])).
% 8.55/1.47  fof(f446,plain,(
% 8.55/1.47    ( ! [X8] : (~r2_hidden(sK3(sK2,X8),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,X8),X8) | k2_relat_1(sK2) = X8) )),
% 8.55/1.47    inference(resolution,[],[f378,f38])).
% 8.55/1.47  fof(f38,plain,(
% 8.55/1.47    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 8.55/1.47    inference(cnf_transformation,[],[f19])).
% 8.55/1.47  fof(f378,plain,(
% 8.55/1.47    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK2) | ~r2_hidden(X0,k1_tarski(sK1))) )),
% 8.55/1.47    inference(superposition,[],[f132,f33])).
% 8.55/1.47  fof(f132,plain,(
% 8.55/1.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X2),k1_tarski(k4_tarski(X0,X1))) | ~r2_hidden(X2,k1_tarski(X1))) )),
% 8.55/1.47    inference(superposition,[],[f59,f52])).
% 8.55/1.47  fof(f59,plain,(
% 8.55/1.47    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3)) )),
% 8.55/1.47    inference(equality_resolution,[],[f48])).
% 8.55/1.47  fof(f48,plain,(
% 8.55/1.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 8.55/1.47    inference(cnf_transformation,[],[f29])).
% 8.55/1.47  fof(f34,plain,(
% 8.55/1.47    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 8.55/1.47    inference(cnf_transformation,[],[f13])).
% 8.55/1.47  % SZS output end Proof for theBenchmark
% 8.55/1.47  % (5141)------------------------------
% 8.55/1.47  % (5141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.55/1.47  % (5141)Termination reason: Refutation
% 8.55/1.47  
% 8.55/1.47  % (5141)Memory used [KB]: 11001
% 8.55/1.47  % (5141)Time elapsed: 1.044 s
% 8.55/1.47  % (5141)------------------------------
% 8.55/1.47  % (5141)------------------------------
% 8.55/1.47  % (5134)Success in time 1.106 s
%------------------------------------------------------------------------------
