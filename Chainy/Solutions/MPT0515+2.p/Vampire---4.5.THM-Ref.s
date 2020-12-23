%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0515+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 386 expanded)
%              Number of leaves         :    9 ( 103 expanded)
%              Depth                    :   22
%              Number of atoms          :  272 (2331 expanded)
%              Number of equality atoms :   22 ( 157 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1517,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1511,f1448])).

fof(f1448,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f1444,f892])).

fof(f892,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f852])).

fof(f852,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f823])).

fof(f823,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f819,f822,f821,f820])).

fof(f820,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f821,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f822,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f819,plain,(
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
    inference(rectify,[],[f818])).

fof(f818,plain,(
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
    inference(nnf_transformation,[],[f647])).

fof(f647,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1444,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK0),sK2) ),
    inference(subsumption_resolution,[],[f1443,f891])).

fof(f891,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f853])).

fof(f853,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f823])).

fof(f1443,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X0,sK0),sK2) ) ),
    inference(subsumption_resolution,[],[f1442,f834])).

fof(f834,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f808])).

fof(f808,plain,
    ( ( ~ r2_hidden(sK0,k2_relat_1(sK2))
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) )
    & ( ( r2_hidden(sK0,k2_relat_1(sK2))
        & r2_hidden(sK0,sK1) )
      | r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f806,f807])).

fof(f807,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK0,k2_relat_1(sK2))
        | ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) )
      & ( ( r2_hidden(sK0,k2_relat_1(sK2))
          & r2_hidden(sK0,sK1) )
        | r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f806,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,k2_relat_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f805])).

fof(f805,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,k2_relat_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f765])).

fof(f765,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f692])).

fof(f692,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f691])).

fof(f691,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

fof(f1442,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X0,sK0),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1441,f937])).

fof(f937,plain,(
    ! [X17] : v1_relat_1(k8_relat_1(X17,sK2)) ),
    inference(resolution,[],[f834,f885])).

fof(f885,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f802])).

fof(f802,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f1441,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X0,sK0),sK2)
      | ~ v1_relat_1(k8_relat_1(sK1,sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1436,f991])).

fof(f991,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f983,f949])).

fof(f949,plain,(
    ! [X28,X26,X27] :
      ( ~ r2_hidden(k4_tarski(X28,X26),k8_relat_1(X27,sK2))
      | r2_hidden(X26,X27) ) ),
    inference(subsumption_resolution,[],[f942,f937])).

fof(f942,plain,(
    ! [X28,X26,X27] :
      ( r2_hidden(X26,X27)
      | ~ r2_hidden(k4_tarski(X28,X26),k8_relat_1(X27,sK2))
      | ~ v1_relat_1(k8_relat_1(X27,sK2)) ) ),
    inference(resolution,[],[f834,f895])).

fof(f895,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f879])).

fof(f879,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f833])).

fof(f833,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK12(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X1)
                    & r2_hidden(sK12(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f831,f832])).

fof(f832,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X1)
          | ~ r2_hidden(sK12(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X1)
            & r2_hidden(sK12(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f831,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f830])).

fof(f830,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f829])).

fof(f829,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f801])).

fof(f801,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f983,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(k4_tarski(sK8(k8_relat_1(sK1,sK2),sK0),sK0),k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f835,f892])).

fof(f835,plain,
    ( r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f808])).

fof(f1436,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X0,sK0),sK2)
      | ~ r2_hidden(sK0,sK1)
      | ~ v1_relat_1(k8_relat_1(sK1,sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f1018,f893])).

fof(f893,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f881])).

fof(f881,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f833])).

fof(f1018,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK0),k8_relat_1(sK1,sK2))
      | ~ r2_hidden(sK0,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f1014,f991])).

fof(f1014,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X0,sK0),k8_relat_1(sK1,sK2)) ) ),
    inference(resolution,[],[f837,f891])).

fof(f837,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f808])).

fof(f1511,plain,(
    r2_hidden(sK0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f1489,f836])).

fof(f836,plain,
    ( r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))
    | r2_hidden(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f808])).

fof(f1489,plain,(
    ! [X2] : ~ r2_hidden(sK0,k2_relat_1(k8_relat_1(X2,sK2))) ),
    inference(resolution,[],[f1454,f892])).

fof(f1454,plain,(
    ! [X6,X5] : ~ r2_hidden(k4_tarski(X5,sK0),k8_relat_1(X6,sK2)) ),
    inference(subsumption_resolution,[],[f1453,f834])).

fof(f1453,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(k4_tarski(X5,sK0),k8_relat_1(X6,sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1451,f937])).

fof(f1451,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(k4_tarski(X5,sK0),k8_relat_1(X6,sK2))
      | ~ v1_relat_1(k8_relat_1(X6,sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f1444,f894])).

fof(f894,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f880])).

fof(f880,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f833])).
%------------------------------------------------------------------------------
