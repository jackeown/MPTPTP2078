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
% DateTime   : Thu Dec  3 12:56:04 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 645 expanded)
%              Number of leaves         :   28 ( 153 expanded)
%              Depth                    :   23
%              Number of atoms          :  855 (3831 expanded)
%              Number of equality atoms :  113 ( 296 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3979,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f120,f568,f1528,f1612,f1725,f1733,f2630,f3879,f3930,f3978])).

fof(f3978,plain,(
    ~ spl12_105 ),
    inference(avatar_contradiction_clause,[],[f3977])).

fof(f3977,plain,
    ( $false
    | ~ spl12_105 ),
    inference(subsumption_resolution,[],[f3976,f61])).

fof(f61,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f3976,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl12_105 ),
    inference(subsumption_resolution,[],[f3969,f126])).

fof(f126,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f125,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f125,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f101,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f3969,plain,
    ( r2_hidden(k3_relat_1(sK2),k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl12_105 ),
    inference(resolution,[],[f3955,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f3955,plain,
    ( r2_hidden(k4_tarski(sK0,k3_relat_1(sK2)),sK2)
    | ~ spl12_105 ),
    inference(resolution,[],[f3937,f719])).

fof(f719,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(k4_tarski(X2,k3_relat_1(sK2)),sK2) ) ),
    inference(superposition,[],[f146,f707])).

fof(f707,plain,(
    k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2)) ),
    inference(resolution,[],[f706,f126])).

fof(f706,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_relat_1(sK2))
      | k1_xboole_0 = k1_wellord1(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f703,f61])).

fof(f703,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_wellord1(sK2,X2)
      | r2_hidden(X2,k3_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f347,f104])).

fof(f347,plain,(
    ! [X10] :
      ( r2_hidden(k4_tarski(sK3(sK2,k1_wellord1(sK2,X10)),X10),sK2)
      | k1_xboole_0 = k1_wellord1(sK2,X10) ) ),
    inference(resolution,[],[f226,f146])).

fof(f226,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X0))
      | k1_xboole_0 = k1_wellord1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f208,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_wellord1(sK2,X0)
      | r2_hidden(sK3(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f207,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

fof(f207,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK2))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f206,f61])).

fof(f206,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK2))
      | r2_hidden(sK3(sK2,X0),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f67,f62])).

fof(f62,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK3(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
      | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(resolution,[],[f106,f61])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
                | sK6(X0,X1,X2) = X1
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
                  & sK6(X0,X1,X2) != X1 )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
          | sK6(X0,X1,X2) = X1
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
            & sK6(X0,X1,X2) != X1 )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f3937,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl12_105 ),
    inference(backward_demodulation,[],[f2095,f3931])).

fof(f3931,plain,
    ( k1_xboole_0 = sK10(sK2,sK0)
    | ~ spl12_105 ),
    inference(resolution,[],[f2095,f1398])).

fof(f1398,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK10(sK2,X0))
      | k1_xboole_0 = sK10(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f1397,f136])).

fof(f136,plain,(
    ! [X0] : r1_tarski(sK10(sK2,X0),k3_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( r1_tarski(sK10(sK2,X0),k3_relat_1(sK2))
      | r1_tarski(sK10(sK2,X0),k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f134,f101])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(sK10(sK2,X0),X1),k3_relat_1(sK2))
      | r1_tarski(sK10(sK2,X0),X1) ) ),
    inference(resolution,[],[f133,f100])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK10(sK2,X1))
      | r2_hidden(X0,k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f96,f61])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,sK10(X0,X1))
      | r2_hidden(X3,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK10(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK10(X0,X1)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK10(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK10(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(f1397,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK10(sK2,X0),k3_relat_1(sK2))
      | ~ r2_hidden(X0,sK10(sK2,X0))
      | k1_xboole_0 = sK10(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f1389])).

fof(f1389,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK10(sK2,X0),k3_relat_1(sK2))
      | ~ r2_hidden(X0,sK10(sK2,X0))
      | k1_xboole_0 = sK10(sK2,X0)
      | k1_xboole_0 = sK10(sK2,X0) ) ),
    inference(resolution,[],[f1371,f225])).

fof(f225,plain,(
    ! [X13] :
      ( r2_hidden(sK3(sK2,sK10(sK2,X13)),sK10(sK2,X13))
      | k1_xboole_0 = sK10(sK2,X13) ) ),
    inference(resolution,[],[f207,f136])).

fof(f1371,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(sK2,X2),sK10(sK2,X3))
      | ~ r1_tarski(X2,k3_relat_1(sK2))
      | ~ r2_hidden(X3,X2)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f1367,f61])).

fof(f1367,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | ~ r1_tarski(X2,k3_relat_1(sK2))
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(sK3(sK2,X2),sK10(sK2,X3))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f699,f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,sK10(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f699,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f698,f61])).

fof(f698,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK2))
      | r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f68,f62])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2095,plain,
    ( r2_hidden(sK0,sK10(sK2,sK0))
    | ~ spl12_105 ),
    inference(avatar_component_clause,[],[f2094])).

fof(f2094,plain,
    ( spl12_105
  <=> r2_hidden(sK0,sK10(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_105])])).

fof(f3930,plain,
    ( spl12_1
    | ~ spl12_30
    | spl12_105 ),
    inference(avatar_contradiction_clause,[],[f3929])).

fof(f3929,plain,
    ( $false
    | spl12_1
    | ~ spl12_30
    | spl12_105 ),
    inference(subsumption_resolution,[],[f3887,f2096])).

fof(f2096,plain,
    ( ~ r2_hidden(sK0,sK10(sK2,sK0))
    | spl12_105 ),
    inference(avatar_component_clause,[],[f2094])).

fof(f3887,plain,
    ( r2_hidden(sK0,sK10(sK2,sK0))
    | spl12_1
    | ~ spl12_30 ),
    inference(backward_demodulation,[],[f611,f563])).

fof(f563,plain,
    ( sK0 = sK1
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl12_30
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f611,plain,
    ( r2_hidden(sK0,sK10(sK2,sK1))
    | spl12_1 ),
    inference(subsumption_resolution,[],[f606,f63])).

fof(f63,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f606,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r2_hidden(sK0,sK10(sK2,sK1))
    | spl12_1 ),
    inference(resolution,[],[f504,f114])).

fof(f114,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl12_1
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f504,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | r2_hidden(X0,sK10(sK2,X1)) ) ),
    inference(resolution,[],[f98,f61])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(X3,sK10(X0,X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f3879,plain,
    ( spl12_1
    | ~ spl12_2
    | spl12_30
    | spl12_79
    | ~ spl12_86 ),
    inference(avatar_contradiction_clause,[],[f3878])).

fof(f3878,plain,
    ( $false
    | spl12_1
    | ~ spl12_2
    | spl12_30
    | spl12_79
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f3865,f1597])).

fof(f1597,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | spl12_79 ),
    inference(avatar_component_clause,[],[f1596])).

fof(f1596,plain,
    ( spl12_79
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_79])])).

fof(f3865,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | spl12_1
    | ~ spl12_2
    | spl12_30
    | ~ spl12_86 ),
    inference(resolution,[],[f3863,f2638])).

fof(f2638,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK0))
        | r2_hidden(X0,k1_wellord1(sK2,sK1)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f117,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f117,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl12_2
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f3863,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl12_1
    | spl12_30
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f3862,f61])).

fof(f3862,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | spl12_1
    | spl12_30
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f3858,f562])).

fof(f562,plain,
    ( sK0 != sK1
    | spl12_30 ),
    inference(avatar_component_clause,[],[f561])).

fof(f3858,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | sK0 = sK1
    | ~ v1_relat_1(sK2)
    | spl12_1
    | spl12_30
    | ~ spl12_86 ),
    inference(resolution,[],[f3854,f105])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X1),X0)
      | r2_hidden(X4,k1_wellord1(X0,X1))
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3854,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | spl12_1
    | spl12_30
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f3853,f562])).

fof(f3853,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | sK0 = sK1
    | spl12_1
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f3852,f64])).

fof(f64,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f3852,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sK0 = sK1
    | spl12_1
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f3844,f63])).

fof(f3844,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sK0 = sK1
    | spl12_1
    | ~ spl12_86 ),
    inference(resolution,[],[f1724,f114])).

fof(f1724,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl12_86 ),
    inference(avatar_component_clause,[],[f1723])).

fof(f1723,plain,
    ( spl12_86
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_86])])).

fof(f2630,plain,
    ( spl12_2
    | ~ spl12_31 ),
    inference(avatar_contradiction_clause,[],[f2629])).

fof(f2629,plain,
    ( $false
    | spl12_2
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f2616,f118])).

fof(f118,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl12_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f2616,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl12_2
    | ~ spl12_31 ),
    inference(resolution,[],[f2588,f101])).

fof(f2588,plain,
    ( r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | spl12_2
    | ~ spl12_31 ),
    inference(resolution,[],[f2562,f1552])).

fof(f1552,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK0),sK2)
    | spl12_2 ),
    inference(resolution,[],[f118,f148])).

fof(f148,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_wellord1(sK2,X1),X2)
      | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X1),X2),X1),sK2) ) ),
    inference(resolution,[],[f146,f100])).

fof(f2562,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(X3,sK0),sK2)
        | r2_hidden(X3,k1_wellord1(sK2,sK1)) )
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f2543,f64])).

fof(f2543,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_wellord1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(X3,sK0),sK2)
        | ~ r2_hidden(sK1,k3_relat_1(sK2)) )
    | ~ spl12_31 ),
    inference(resolution,[],[f1213,f567])).

fof(f567,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl12_31
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f1213,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
      | r2_hidden(X2,k1_wellord1(sK2,X1))
      | ~ r2_hidden(k4_tarski(X2,X0),sK2)
      | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f1212,f61])).

fof(f1212,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
      | ~ v1_relat_1(sK2)
      | r2_hidden(X2,k1_wellord1(sK2,X1))
      | ~ r2_hidden(k4_tarski(X2,X0),sK2)
      | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f121,f62])).

fof(f121,plain,(
    ! [X6,X7,X5,X1] :
      ( ~ v2_wellord1(X1)
      | ~ r2_hidden(X5,k1_wellord1(X1,X7))
      | ~ v1_relat_1(X1)
      | r2_hidden(X6,k1_wellord1(X1,X7))
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X7,k3_relat_1(X1)) ) ),
    inference(global_subsumption,[],[f87,f109])).

fof(f109,plain,(
    ! [X6,X7,X5,X1] :
      ( r2_hidden(X6,k1_wellord1(X1,X7))
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,k1_wellord1(X1,X7))
      | ~ r2_hidden(X7,k3_relat_1(X1))
      | ~ r1_tarski(k1_wellord1(X1,X7),k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k1_wellord1(X1,X7) != X0
      | ~ r2_hidden(X7,k3_relat_1(X1))
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_wellord1(X1,sK7(X0,X1)) = X0
            & r2_hidden(sK7(X0,X1),k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ( ~ r2_hidden(sK9(X0,X1),X0)
            & r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X1)
            & r2_hidden(sK8(X0,X1),X0) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r2_hidden(X6,X0)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1) )
              | ~ r2_hidden(X5,X0) )
          | ( ! [X7] :
                ( k1_wellord1(X1,X7) != X0
                | ~ r2_hidden(X7,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f48,f51,f50,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_wellord1(X1,X2) = X0
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( k1_wellord1(X1,sK7(X0,X1)) = X0
        & r2_hidden(sK7(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,X0)
              & r2_hidden(k4_tarski(X4,X3),X1) )
          & r2_hidden(X3,X0) )
     => ( ? [X4] :
            ( ~ r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,sK8(X0,X1)),X1) )
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,sK8(X0,X1)),X1) )
     => ( ~ r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r2_hidden(X6,X0)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1) )
              | ~ r2_hidden(X5,X0) )
          | ( ! [X7] :
                ( k1_wellord1(X1,X7) != X0
                | ~ r2_hidden(X7,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X0) )
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X0) )
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X3] :
              ( r2_hidden(X3,X0)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X1)
                 => r2_hidden(X4,X0) ) ) ) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X2] :
              ( r2_hidden(X2,X0)
             => ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X2),X1)
                 => r2_hidden(X3,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_wellord1)).

fof(f1733,plain,(
    spl12_85 ),
    inference(avatar_contradiction_clause,[],[f1732])).

fof(f1732,plain,
    ( $false
    | spl12_85 ),
    inference(subsumption_resolution,[],[f1731,f61])).

fof(f1731,plain,
    ( ~ v1_relat_1(sK2)
    | spl12_85 ),
    inference(subsumption_resolution,[],[f1728,f62])).

fof(f1728,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_85 ),
    inference(resolution,[],[f1721,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f1721,plain,
    ( ~ v6_relat_2(sK2)
    | spl12_85 ),
    inference(avatar_component_clause,[],[f1719])).

fof(f1719,plain,
    ( spl12_85
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_85])])).

fof(f1725,plain,
    ( ~ spl12_85
    | spl12_86 ),
    inference(avatar_split_clause,[],[f1717,f1723,f1719])).

fof(f1717,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | ~ v6_relat_2(sK2)
      | r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    inference(resolution,[],[f69,f61])).

fof(f69,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
            & sK4(X0) != sK5(X0)
            & r2_hidden(sK5(X0),k3_relat_1(X0))
            & r2_hidden(sK4(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
        & sK4(X0) != sK5(X0)
        & r2_hidden(sK5(X0),k3_relat_1(X0))
        & r2_hidden(sK4(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f1612,plain,(
    ~ spl12_79 ),
    inference(avatar_contradiction_clause,[],[f1611])).

fof(f1611,plain,
    ( $false
    | ~ spl12_79 ),
    inference(subsumption_resolution,[],[f1610,f61])).

fof(f1610,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl12_79 ),
    inference(resolution,[],[f1598,f108])).

fof(f108,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1598,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl12_79 ),
    inference(avatar_component_clause,[],[f1596])).

fof(f1528,plain,
    ( spl12_2
    | ~ spl12_30 ),
    inference(avatar_contradiction_clause,[],[f1527])).

fof(f1527,plain,
    ( $false
    | spl12_2
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f1526,f125])).

fof(f1526,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl12_2
    | ~ spl12_30 ),
    inference(forward_demodulation,[],[f118,f563])).

fof(f568,plain,
    ( spl12_30
    | spl12_31
    | ~ spl12_1 ),
    inference(avatar_split_clause,[],[f559,f112,f565,f561])).

fof(f559,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | sK0 = sK1
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f555,f61])).

fof(f555,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | sK0 = sK1
    | ~ v1_relat_1(sK2)
    | ~ spl12_1 ),
    inference(resolution,[],[f113,f105])).

fof(f113,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f120,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f65,f116,f112])).

fof(f65,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f119,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f66,f116,f112])).

fof(f66,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7937)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (7951)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (7953)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (7943)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (7945)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (7959)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (7938)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (7948)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (7940)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (7941)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (7950)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (7958)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (7936)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (7939)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (7962)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (7964)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (7965)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (7942)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (7954)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (7956)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (7957)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (7955)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (7961)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (7952)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (7946)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (7960)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (7947)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (7949)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (7944)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (7958)Refutation not found, incomplete strategy% (7958)------------------------------
% 0.20/0.54  % (7958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7958)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (7958)Memory used [KB]: 10874
% 0.20/0.54  % (7958)Time elapsed: 0.097 s
% 0.20/0.54  % (7958)------------------------------
% 0.20/0.54  % (7958)------------------------------
% 0.20/0.55  % (7963)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.24/0.71  % (7966)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.22/0.81  % (7939)Refutation found. Thanks to Tanya!
% 3.22/0.81  % SZS status Theorem for theBenchmark
% 3.22/0.81  % SZS output start Proof for theBenchmark
% 3.22/0.81  fof(f3979,plain,(
% 3.22/0.81    $false),
% 3.22/0.81    inference(avatar_sat_refutation,[],[f119,f120,f568,f1528,f1612,f1725,f1733,f2630,f3879,f3930,f3978])).
% 3.22/0.81  fof(f3978,plain,(
% 3.22/0.81    ~spl12_105),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f3977])).
% 3.22/0.81  fof(f3977,plain,(
% 3.22/0.81    $false | ~spl12_105),
% 3.22/0.81    inference(subsumption_resolution,[],[f3976,f61])).
% 3.22/0.81  fof(f61,plain,(
% 3.22/0.81    v1_relat_1(sK2)),
% 3.22/0.81    inference(cnf_transformation,[],[f32])).
% 3.22/0.81  fof(f32,plain,(
% 3.22/0.81    (~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).
% 3.22/0.81  fof(f31,plain,(
% 3.22/0.81    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f30,plain,(
% 3.22/0.81    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 3.22/0.81    inference(flattening,[],[f29])).
% 3.22/0.81  fof(f29,plain,(
% 3.22/0.81    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 3.22/0.81    inference(nnf_transformation,[],[f15])).
% 3.22/0.81  fof(f15,plain,(
% 3.22/0.81    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 3.22/0.81    inference(flattening,[],[f14])).
% 3.22/0.81  fof(f14,plain,(
% 3.22/0.81    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 3.22/0.81    inference(ennf_transformation,[],[f12])).
% 3.22/0.81  fof(f12,negated_conjecture,(
% 3.22/0.81    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 3.22/0.81    inference(negated_conjecture,[],[f11])).
% 3.22/0.81  fof(f11,conjecture,(
% 3.22/0.81    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).
% 3.22/0.81  fof(f3976,plain,(
% 3.22/0.81    ~v1_relat_1(sK2) | ~spl12_105),
% 3.22/0.81    inference(subsumption_resolution,[],[f3969,f126])).
% 3.22/0.81  fof(f126,plain,(
% 3.22/0.81    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 3.22/0.81    inference(resolution,[],[f125,f102])).
% 3.22/0.81  fof(f102,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f26])).
% 3.22/0.81  fof(f26,plain,(
% 3.22/0.81    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.22/0.81    inference(ennf_transformation,[],[f3])).
% 3.22/0.81  fof(f3,axiom,(
% 3.22/0.81    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.22/0.81  fof(f125,plain,(
% 3.22/0.81    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f124])).
% 3.22/0.81  fof(f124,plain,(
% 3.22/0.81    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 3.22/0.81    inference(resolution,[],[f101,f100])).
% 3.22/0.81  fof(f100,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f60])).
% 3.22/0.81  fof(f60,plain,(
% 3.22/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f58,f59])).
% 3.22/0.81  fof(f59,plain,(
% 3.22/0.81    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0)))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f58,plain,(
% 3.22/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.22/0.81    inference(rectify,[],[f57])).
% 3.22/0.81  fof(f57,plain,(
% 3.22/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.22/0.81    inference(nnf_transformation,[],[f25])).
% 3.22/0.81  fof(f25,plain,(
% 3.22/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f1])).
% 3.22/0.81  fof(f1,axiom,(
% 3.22/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.22/0.81  fof(f101,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r2_hidden(sK11(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f60])).
% 3.22/0.81  fof(f3969,plain,(
% 3.22/0.81    r2_hidden(k3_relat_1(sK2),k3_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl12_105),
% 3.22/0.81    inference(resolution,[],[f3955,f104])).
% 3.22/0.81  fof(f104,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f28])).
% 3.22/0.81  fof(f28,plain,(
% 3.22/0.81    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.22/0.81    inference(flattening,[],[f27])).
% 3.22/0.81  fof(f27,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.22/0.81    inference(ennf_transformation,[],[f2])).
% 3.22/0.81  fof(f2,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 3.22/0.81  fof(f3955,plain,(
% 3.22/0.81    r2_hidden(k4_tarski(sK0,k3_relat_1(sK2)),sK2) | ~spl12_105),
% 3.22/0.81    inference(resolution,[],[f3937,f719])).
% 3.22/0.81  fof(f719,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(k4_tarski(X2,k3_relat_1(sK2)),sK2)) )),
% 3.22/0.81    inference(superposition,[],[f146,f707])).
% 3.22/0.81  fof(f707,plain,(
% 3.22/0.81    k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2))),
% 3.22/0.81    inference(resolution,[],[f706,f126])).
% 3.22/0.81  fof(f706,plain,(
% 3.22/0.81    ( ! [X2] : (r2_hidden(X2,k3_relat_1(sK2)) | k1_xboole_0 = k1_wellord1(sK2,X2)) )),
% 3.22/0.81    inference(subsumption_resolution,[],[f703,f61])).
% 3.22/0.81  fof(f703,plain,(
% 3.22/0.81    ( ! [X2] : (k1_xboole_0 = k1_wellord1(sK2,X2) | r2_hidden(X2,k3_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 3.22/0.81    inference(resolution,[],[f347,f104])).
% 3.22/0.81  fof(f347,plain,(
% 3.22/0.81    ( ! [X10] : (r2_hidden(k4_tarski(sK3(sK2,k1_wellord1(sK2,X10)),X10),sK2) | k1_xboole_0 = k1_wellord1(sK2,X10)) )),
% 3.22/0.81    inference(resolution,[],[f226,f146])).
% 3.22/0.81  fof(f226,plain,(
% 3.22/0.81    ( ! [X0] : (r2_hidden(sK3(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X0)) | k1_xboole_0 = k1_wellord1(sK2,X0)) )),
% 3.22/0.81    inference(subsumption_resolution,[],[f208,f61])).
% 3.22/0.81  fof(f208,plain,(
% 3.22/0.81    ( ! [X0] : (k1_xboole_0 = k1_wellord1(sK2,X0) | r2_hidden(sK3(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X0)) | ~v1_relat_1(sK2)) )),
% 3.22/0.81    inference(resolution,[],[f207,f87])).
% 3.22/0.81  fof(f87,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f21])).
% 3.22/0.81  fof(f21,plain,(
% 3.22/0.81    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.22/0.81    inference(ennf_transformation,[],[f9])).
% 3.22/0.81  fof(f9,axiom,(
% 3.22/0.81    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).
% 3.22/0.81  fof(f207,plain,(
% 3.22/0.81    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK2)) | k1_xboole_0 = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 3.22/0.81    inference(subsumption_resolution,[],[f206,f61])).
% 3.22/0.81  fof(f206,plain,(
% 3.22/0.81    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK2)) | r2_hidden(sK3(sK2,X0),X0) | ~v1_relat_1(sK2)) )),
% 3.22/0.81    inference(resolution,[],[f67,f62])).
% 3.22/0.81  fof(f62,plain,(
% 3.22/0.81    v2_wellord1(sK2)),
% 3.22/0.81    inference(cnf_transformation,[],[f32])).
% 3.22/0.81  fof(f67,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~v2_wellord1(X0) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | r2_hidden(sK3(X0,X1),X1) | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f34])).
% 3.22/0.81  fof(f34,plain,(
% 3.22/0.81    ! [X0] : (! [X1] : ((! [X3] : (r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f33])).
% 3.22/0.81  fof(f33,plain,(
% 3.22/0.81    ! [X1,X0] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X1)))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f17,plain,(
% 3.22/0.81    ! [X0] : (! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(flattening,[],[f16])).
% 3.22/0.81  fof(f16,plain,(
% 3.22/0.81    ! [X0] : ((! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f8])).
% 3.22/0.81  fof(f8,axiom,(
% 3.22/0.81    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).
% 3.22/0.81  fof(f146,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 3.22/0.81    inference(resolution,[],[f106,f61])).
% 3.22/0.81  fof(f106,plain,(
% 3.22/0.81    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 3.22/0.81    inference(equality_resolution,[],[f82])).
% 3.22/0.81  fof(f82,plain,(
% 3.22/0.81    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f45])).
% 3.22/0.81  fof(f45,plain,(
% 3.22/0.81    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) | sK6(X0,X1,X2) = X1 | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) & sK6(X0,X1,X2) != X1) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 3.22/0.81  fof(f44,plain,(
% 3.22/0.81    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) | sK6(X0,X1,X2) = X1 | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) & sK6(X0,X1,X2) != X1) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f43,plain,(
% 3.22/0.81    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(rectify,[],[f42])).
% 3.22/0.81  fof(f42,plain,(
% 3.22/0.81    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(flattening,[],[f41])).
% 3.22/0.81  fof(f41,plain,(
% 3.22/0.81    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(nnf_transformation,[],[f20])).
% 3.22/0.81  fof(f20,plain,(
% 3.22/0.81    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f4])).
% 3.22/0.81  fof(f4,axiom,(
% 3.22/0.81    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 3.22/0.81  fof(f3937,plain,(
% 3.22/0.81    r2_hidden(sK0,k1_xboole_0) | ~spl12_105),
% 3.22/0.81    inference(backward_demodulation,[],[f2095,f3931])).
% 3.22/0.81  fof(f3931,plain,(
% 3.22/0.81    k1_xboole_0 = sK10(sK2,sK0) | ~spl12_105),
% 3.22/0.81    inference(resolution,[],[f2095,f1398])).
% 3.22/0.81  fof(f1398,plain,(
% 3.22/0.81    ( ! [X0] : (~r2_hidden(X0,sK10(sK2,X0)) | k1_xboole_0 = sK10(sK2,X0)) )),
% 3.22/0.81    inference(subsumption_resolution,[],[f1397,f136])).
% 3.22/0.81  fof(f136,plain,(
% 3.22/0.81    ( ! [X0] : (r1_tarski(sK10(sK2,X0),k3_relat_1(sK2))) )),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f135])).
% 3.22/0.81  fof(f135,plain,(
% 3.22/0.81    ( ! [X0] : (r1_tarski(sK10(sK2,X0),k3_relat_1(sK2)) | r1_tarski(sK10(sK2,X0),k3_relat_1(sK2))) )),
% 3.22/0.81    inference(resolution,[],[f134,f101])).
% 3.22/0.81  fof(f134,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r2_hidden(sK11(sK10(sK2,X0),X1),k3_relat_1(sK2)) | r1_tarski(sK10(sK2,X0),X1)) )),
% 3.22/0.81    inference(resolution,[],[f133,f100])).
% 3.22/0.81  fof(f133,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r2_hidden(X0,sK10(sK2,X1)) | r2_hidden(X0,k3_relat_1(sK2))) )),
% 3.22/0.81    inference(resolution,[],[f96,f61])).
% 3.22/0.81  fof(f96,plain,(
% 3.22/0.81    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(X3,sK10(X0,X1)) | r2_hidden(X3,k3_relat_1(X0))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f56])).
% 3.22/0.81  fof(f56,plain,(
% 3.22/0.81    ! [X0,X1] : (! [X3] : ((r2_hidden(X3,sK10(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK10(X0,X1)))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f54,f55])).
% 3.22/0.81  fof(f55,plain,(
% 3.22/0.81    ! [X1,X0] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) => ! [X3] : ((r2_hidden(X3,sK10(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK10(X0,X1)))))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f54,plain,(
% 3.22/0.81    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(flattening,[],[f53])).
% 3.22/0.81  fof(f53,plain,(
% 3.22/0.81    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(nnf_transformation,[],[f24])).
% 3.22/0.81  fof(f24,plain,(
% 3.22/0.81    ! [X0,X1] : (? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f7])).
% 3.22/0.81  fof(f7,axiom,(
% 3.22/0.81    ! [X0,X1] : (v1_relat_1(X0) => ? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).
% 3.22/0.81  fof(f1397,plain,(
% 3.22/0.81    ( ! [X0] : (~r1_tarski(sK10(sK2,X0),k3_relat_1(sK2)) | ~r2_hidden(X0,sK10(sK2,X0)) | k1_xboole_0 = sK10(sK2,X0)) )),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f1389])).
% 3.22/0.81  fof(f1389,plain,(
% 3.22/0.81    ( ! [X0] : (~r1_tarski(sK10(sK2,X0),k3_relat_1(sK2)) | ~r2_hidden(X0,sK10(sK2,X0)) | k1_xboole_0 = sK10(sK2,X0) | k1_xboole_0 = sK10(sK2,X0)) )),
% 3.22/0.81    inference(resolution,[],[f1371,f225])).
% 3.22/0.81  fof(f225,plain,(
% 3.22/0.81    ( ! [X13] : (r2_hidden(sK3(sK2,sK10(sK2,X13)),sK10(sK2,X13)) | k1_xboole_0 = sK10(sK2,X13)) )),
% 3.22/0.81    inference(resolution,[],[f207,f136])).
% 3.22/0.81  fof(f1371,plain,(
% 3.22/0.81    ( ! [X2,X3] : (~r2_hidden(sK3(sK2,X2),sK10(sK2,X3)) | ~r1_tarski(X2,k3_relat_1(sK2)) | ~r2_hidden(X3,X2) | k1_xboole_0 = X2) )),
% 3.22/0.81    inference(subsumption_resolution,[],[f1367,f61])).
% 3.22/0.81  fof(f1367,plain,(
% 3.22/0.81    ( ! [X2,X3] : (k1_xboole_0 = X2 | ~r1_tarski(X2,k3_relat_1(sK2)) | ~r2_hidden(X3,X2) | ~r2_hidden(sK3(sK2,X2),sK10(sK2,X3)) | ~v1_relat_1(sK2)) )),
% 3.22/0.81    inference(resolution,[],[f699,f97])).
% 3.22/0.81  fof(f97,plain,(
% 3.22/0.81    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,sK10(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f56])).
% 3.22/0.81  fof(f699,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,X1)) )),
% 3.22/0.81    inference(subsumption_resolution,[],[f698,f61])).
% 3.22/0.81  fof(f698,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2) | ~v1_relat_1(sK2)) )),
% 3.22/0.81    inference(resolution,[],[f68,f62])).
% 3.22/0.81  fof(f68,plain,(
% 3.22/0.81    ( ! [X0,X3,X1] : (~v2_wellord1(X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f34])).
% 3.22/0.81  fof(f2095,plain,(
% 3.22/0.81    r2_hidden(sK0,sK10(sK2,sK0)) | ~spl12_105),
% 3.22/0.81    inference(avatar_component_clause,[],[f2094])).
% 3.22/0.81  fof(f2094,plain,(
% 3.22/0.81    spl12_105 <=> r2_hidden(sK0,sK10(sK2,sK0))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_105])])).
% 3.22/0.81  fof(f3930,plain,(
% 3.22/0.81    spl12_1 | ~spl12_30 | spl12_105),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f3929])).
% 3.22/0.81  fof(f3929,plain,(
% 3.22/0.81    $false | (spl12_1 | ~spl12_30 | spl12_105)),
% 3.22/0.81    inference(subsumption_resolution,[],[f3887,f2096])).
% 3.22/0.81  fof(f2096,plain,(
% 3.22/0.81    ~r2_hidden(sK0,sK10(sK2,sK0)) | spl12_105),
% 3.22/0.81    inference(avatar_component_clause,[],[f2094])).
% 3.22/0.81  fof(f3887,plain,(
% 3.22/0.81    r2_hidden(sK0,sK10(sK2,sK0)) | (spl12_1 | ~spl12_30)),
% 3.22/0.81    inference(backward_demodulation,[],[f611,f563])).
% 3.22/0.81  fof(f563,plain,(
% 3.22/0.81    sK0 = sK1 | ~spl12_30),
% 3.22/0.81    inference(avatar_component_clause,[],[f561])).
% 3.22/0.81  fof(f561,plain,(
% 3.22/0.81    spl12_30 <=> sK0 = sK1),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).
% 3.22/0.81  fof(f611,plain,(
% 3.22/0.81    r2_hidden(sK0,sK10(sK2,sK1)) | spl12_1),
% 3.22/0.81    inference(subsumption_resolution,[],[f606,f63])).
% 3.22/0.81  fof(f63,plain,(
% 3.22/0.81    r2_hidden(sK0,k3_relat_1(sK2))),
% 3.22/0.81    inference(cnf_transformation,[],[f32])).
% 3.22/0.81  fof(f606,plain,(
% 3.22/0.81    ~r2_hidden(sK0,k3_relat_1(sK2)) | r2_hidden(sK0,sK10(sK2,sK1)) | spl12_1),
% 3.22/0.81    inference(resolution,[],[f504,f114])).
% 3.22/0.81  fof(f114,plain,(
% 3.22/0.81    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | spl12_1),
% 3.22/0.81    inference(avatar_component_clause,[],[f112])).
% 3.22/0.81  fof(f112,plain,(
% 3.22/0.81    spl12_1 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 3.22/0.81  fof(f504,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(X0,sK10(sK2,X1))) )),
% 3.22/0.81    inference(resolution,[],[f98,f61])).
% 3.22/0.81  fof(f98,plain,(
% 3.22/0.81    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)) | r2_hidden(X3,sK10(X0,X1))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f56])).
% 3.22/0.81  fof(f3879,plain,(
% 3.22/0.81    spl12_1 | ~spl12_2 | spl12_30 | spl12_79 | ~spl12_86),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f3878])).
% 3.22/0.81  fof(f3878,plain,(
% 3.22/0.81    $false | (spl12_1 | ~spl12_2 | spl12_30 | spl12_79 | ~spl12_86)),
% 3.22/0.81    inference(subsumption_resolution,[],[f3865,f1597])).
% 3.22/0.81  fof(f1597,plain,(
% 3.22/0.81    ~r2_hidden(sK1,k1_wellord1(sK2,sK1)) | spl12_79),
% 3.22/0.81    inference(avatar_component_clause,[],[f1596])).
% 3.22/0.81  fof(f1596,plain,(
% 3.22/0.81    spl12_79 <=> r2_hidden(sK1,k1_wellord1(sK2,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_79])])).
% 3.22/0.81  fof(f3865,plain,(
% 3.22/0.81    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | (spl12_1 | ~spl12_2 | spl12_30 | ~spl12_86)),
% 3.22/0.81    inference(resolution,[],[f3863,f2638])).
% 3.22/0.81  fof(f2638,plain,(
% 3.22/0.81    ( ! [X0] : (~r2_hidden(X0,k1_wellord1(sK2,sK0)) | r2_hidden(X0,k1_wellord1(sK2,sK1))) ) | ~spl12_2),
% 3.22/0.81    inference(resolution,[],[f117,f99])).
% 3.22/0.81  fof(f99,plain,(
% 3.22/0.81    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f60])).
% 3.22/0.81  fof(f117,plain,(
% 3.22/0.81    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl12_2),
% 3.22/0.81    inference(avatar_component_clause,[],[f116])).
% 3.22/0.81  fof(f116,plain,(
% 3.22/0.81    spl12_2 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 3.22/0.81  fof(f3863,plain,(
% 3.22/0.81    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | (spl12_1 | spl12_30 | ~spl12_86)),
% 3.22/0.81    inference(subsumption_resolution,[],[f3862,f61])).
% 3.22/0.81  fof(f3862,plain,(
% 3.22/0.81    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~v1_relat_1(sK2) | (spl12_1 | spl12_30 | ~spl12_86)),
% 3.22/0.81    inference(subsumption_resolution,[],[f3858,f562])).
% 3.22/0.81  fof(f562,plain,(
% 3.22/0.81    sK0 != sK1 | spl12_30),
% 3.22/0.81    inference(avatar_component_clause,[],[f561])).
% 3.22/0.81  fof(f3858,plain,(
% 3.22/0.81    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | sK0 = sK1 | ~v1_relat_1(sK2) | (spl12_1 | spl12_30 | ~spl12_86)),
% 3.22/0.81    inference(resolution,[],[f3854,f105])).
% 3.22/0.81  fof(f105,plain,(
% 3.22/0.81    ( ! [X4,X0,X1] : (~r2_hidden(k4_tarski(X4,X1),X0) | r2_hidden(X4,k1_wellord1(X0,X1)) | X1 = X4 | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(equality_resolution,[],[f83])).
% 3.22/0.81  fof(f83,plain,(
% 3.22/0.81    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f45])).
% 3.22/0.81  fof(f3854,plain,(
% 3.22/0.81    r2_hidden(k4_tarski(sK1,sK0),sK2) | (spl12_1 | spl12_30 | ~spl12_86)),
% 3.22/0.81    inference(subsumption_resolution,[],[f3853,f562])).
% 3.22/0.81  fof(f3853,plain,(
% 3.22/0.81    r2_hidden(k4_tarski(sK1,sK0),sK2) | sK0 = sK1 | (spl12_1 | ~spl12_86)),
% 3.22/0.81    inference(subsumption_resolution,[],[f3852,f64])).
% 3.22/0.81  fof(f64,plain,(
% 3.22/0.81    r2_hidden(sK1,k3_relat_1(sK2))),
% 3.22/0.81    inference(cnf_transformation,[],[f32])).
% 3.22/0.81  fof(f3852,plain,(
% 3.22/0.81    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2)) | sK0 = sK1 | (spl12_1 | ~spl12_86)),
% 3.22/0.81    inference(subsumption_resolution,[],[f3844,f63])).
% 3.22/0.81  fof(f3844,plain,(
% 3.22/0.81    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | sK0 = sK1 | (spl12_1 | ~spl12_86)),
% 3.22/0.81    inference(resolution,[],[f1724,f114])).
% 3.22/0.81  fof(f1724,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1) ) | ~spl12_86),
% 3.22/0.81    inference(avatar_component_clause,[],[f1723])).
% 3.22/0.81  fof(f1723,plain,(
% 3.22/0.81    spl12_86 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_86])])).
% 3.22/0.81  fof(f2630,plain,(
% 3.22/0.81    spl12_2 | ~spl12_31),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f2629])).
% 3.22/0.81  fof(f2629,plain,(
% 3.22/0.81    $false | (spl12_2 | ~spl12_31)),
% 3.22/0.81    inference(subsumption_resolution,[],[f2616,f118])).
% 3.22/0.81  fof(f118,plain,(
% 3.22/0.81    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl12_2),
% 3.22/0.81    inference(avatar_component_clause,[],[f116])).
% 3.22/0.81  fof(f2616,plain,(
% 3.22/0.81    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (spl12_2 | ~spl12_31)),
% 3.22/0.81    inference(resolution,[],[f2588,f101])).
% 3.22/0.81  fof(f2588,plain,(
% 3.22/0.81    r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | (spl12_2 | ~spl12_31)),
% 3.22/0.81    inference(resolution,[],[f2562,f1552])).
% 3.22/0.81  fof(f1552,plain,(
% 3.22/0.81    r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK0),sK2) | spl12_2),
% 3.22/0.81    inference(resolution,[],[f118,f148])).
% 3.22/0.81  fof(f148,plain,(
% 3.22/0.81    ( ! [X2,X1] : (r1_tarski(k1_wellord1(sK2,X1),X2) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X1),X2),X1),sK2)) )),
% 3.22/0.81    inference(resolution,[],[f146,f100])).
% 3.22/0.81  fof(f2562,plain,(
% 3.22/0.81    ( ! [X3] : (~r2_hidden(k4_tarski(X3,sK0),sK2) | r2_hidden(X3,k1_wellord1(sK2,sK1))) ) | ~spl12_31),
% 3.22/0.81    inference(subsumption_resolution,[],[f2543,f64])).
% 3.22/0.81  fof(f2543,plain,(
% 3.22/0.81    ( ! [X3] : (r2_hidden(X3,k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(X3,sK0),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2))) ) | ~spl12_31),
% 3.22/0.81    inference(resolution,[],[f1213,f567])).
% 3.22/0.81  fof(f567,plain,(
% 3.22/0.81    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl12_31),
% 3.22/0.81    inference(avatar_component_clause,[],[f565])).
% 3.22/0.81  fof(f565,plain,(
% 3.22/0.81    spl12_31 <=> r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).
% 3.22/0.81  fof(f1213,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | r2_hidden(X2,k1_wellord1(sK2,X1)) | ~r2_hidden(k4_tarski(X2,X0),sK2) | ~r2_hidden(X1,k3_relat_1(sK2))) )),
% 3.22/0.81    inference(subsumption_resolution,[],[f1212,f61])).
% 3.22/0.81  fof(f1212,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | ~v1_relat_1(sK2) | r2_hidden(X2,k1_wellord1(sK2,X1)) | ~r2_hidden(k4_tarski(X2,X0),sK2) | ~r2_hidden(X1,k3_relat_1(sK2))) )),
% 3.22/0.81    inference(resolution,[],[f121,f62])).
% 3.22/0.81  fof(f121,plain,(
% 3.22/0.81    ( ! [X6,X7,X5,X1] : (~v2_wellord1(X1) | ~r2_hidden(X5,k1_wellord1(X1,X7)) | ~v1_relat_1(X1) | r2_hidden(X6,k1_wellord1(X1,X7)) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X7,k3_relat_1(X1))) )),
% 3.22/0.81    inference(global_subsumption,[],[f87,f109])).
% 3.22/0.81  fof(f109,plain,(
% 3.22/0.81    ( ! [X6,X7,X5,X1] : (r2_hidden(X6,k1_wellord1(X1,X7)) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,k1_wellord1(X1,X7)) | ~r2_hidden(X7,k3_relat_1(X1)) | ~r1_tarski(k1_wellord1(X1,X7),k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 3.22/0.81    inference(equality_resolution,[],[f89])).
% 3.22/0.81  fof(f89,plain,(
% 3.22/0.81    ( ! [X6,X0,X7,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,X0) | k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1)) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f52])).
% 3.22/0.81  fof(f52,plain,(
% 3.22/0.81    ! [X0,X1] : ((((k1_wellord1(X1,sK7(X0,X1)) = X0 & r2_hidden(sK7(X0,X1),k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ((~r2_hidden(sK9(X0,X1),X0) & r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X1)) & r2_hidden(sK8(X0,X1),X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f48,f51,f50,f49])).
% 3.22/0.81  fof(f49,plain,(
% 3.22/0.81    ! [X1,X0] : (? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) => (k1_wellord1(X1,sK7(X0,X1)) = X0 & r2_hidden(sK7(X0,X1),k3_relat_1(X1))))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f50,plain,(
% 3.22/0.81    ! [X1,X0] : (? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0)) => (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,sK8(X0,X1)),X1)) & r2_hidden(sK8(X0,X1),X0)))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f51,plain,(
% 3.22/0.81    ! [X1,X0] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,sK8(X0,X1)),X1)) => (~r2_hidden(sK9(X0,X1),X0) & r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X1)))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f48,plain,(
% 3.22/0.81    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 3.22/0.81    inference(rectify,[],[f47])).
% 3.22/0.81  fof(f47,plain,(
% 3.22/0.81    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 3.22/0.81    inference(flattening,[],[f46])).
% 3.22/0.81  fof(f46,plain,(
% 3.22/0.81    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 3.22/0.81    inference(nnf_transformation,[],[f23])).
% 3.22/0.81  fof(f23,plain,(
% 3.22/0.81    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 3.22/0.81    inference(flattening,[],[f22])).
% 3.22/0.81  fof(f22,plain,(
% 3.22/0.81    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 3.22/0.81    inference(ennf_transformation,[],[f13])).
% 3.22/0.81  fof(f13,plain,(
% 3.22/0.81    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 3.22/0.81    inference(rectify,[],[f10])).
% 3.22/0.81  fof(f10,axiom,(
% 3.22/0.81    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_wellord1)).
% 3.22/0.81  fof(f1733,plain,(
% 3.22/0.81    spl12_85),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f1732])).
% 3.22/0.81  fof(f1732,plain,(
% 3.22/0.81    $false | spl12_85),
% 3.22/0.81    inference(subsumption_resolution,[],[f1731,f61])).
% 3.22/0.81  fof(f1731,plain,(
% 3.22/0.81    ~v1_relat_1(sK2) | spl12_85),
% 3.22/0.81    inference(subsumption_resolution,[],[f1728,f62])).
% 3.22/0.81  fof(f1728,plain,(
% 3.22/0.81    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl12_85),
% 3.22/0.81    inference(resolution,[],[f1721,f78])).
% 3.22/0.81  fof(f78,plain,(
% 3.22/0.81    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f40])).
% 3.22/0.81  fof(f40,plain,(
% 3.22/0.81    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(flattening,[],[f39])).
% 3.22/0.81  fof(f39,plain,(
% 3.22/0.81    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(nnf_transformation,[],[f19])).
% 3.22/0.81  fof(f19,plain,(
% 3.22/0.81    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f5])).
% 3.22/0.81  fof(f5,axiom,(
% 3.22/0.81    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 3.22/0.81  fof(f1721,plain,(
% 3.22/0.81    ~v6_relat_2(sK2) | spl12_85),
% 3.22/0.81    inference(avatar_component_clause,[],[f1719])).
% 3.22/0.81  fof(f1719,plain,(
% 3.22/0.81    spl12_85 <=> v6_relat_2(sK2)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_85])])).
% 3.22/0.81  fof(f1725,plain,(
% 3.22/0.81    ~spl12_85 | spl12_86),
% 3.22/0.81    inference(avatar_split_clause,[],[f1717,f1723,f1719])).
% 3.22/0.81  fof(f1717,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~v6_relat_2(sK2) | r2_hidden(k4_tarski(X1,X0),sK2)) )),
% 3.22/0.81    inference(resolution,[],[f69,f61])).
% 3.22/0.81  fof(f69,plain,(
% 3.22/0.81    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | r2_hidden(k4_tarski(X4,X3),X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f38])).
% 3.22/0.81  fof(f38,plain,(
% 3.22/0.81    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) & ~r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) & sK4(X0) != sK5(X0) & r2_hidden(sK5(X0),k3_relat_1(X0)) & r2_hidden(sK4(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f37])).
% 3.22/0.81  fof(f37,plain,(
% 3.22/0.81    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) & ~r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) & sK4(X0) != sK5(X0) & r2_hidden(sK5(X0),k3_relat_1(X0)) & r2_hidden(sK4(X0),k3_relat_1(X0))))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f36,plain,(
% 3.22/0.81    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(rectify,[],[f35])).
% 3.22/0.81  fof(f35,plain,(
% 3.22/0.81    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(nnf_transformation,[],[f18])).
% 3.22/0.81  fof(f18,plain,(
% 3.22/0.81    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f6])).
% 3.22/0.81  fof(f6,axiom,(
% 3.22/0.81    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).
% 3.22/0.81  fof(f1612,plain,(
% 3.22/0.81    ~spl12_79),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f1611])).
% 3.22/0.81  fof(f1611,plain,(
% 3.22/0.81    $false | ~spl12_79),
% 3.22/0.81    inference(subsumption_resolution,[],[f1610,f61])).
% 3.22/0.81  fof(f1610,plain,(
% 3.22/0.81    ~v1_relat_1(sK2) | ~spl12_79),
% 3.22/0.81    inference(resolution,[],[f1598,f108])).
% 3.22/0.81  fof(f108,plain,(
% 3.22/0.81    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(equality_resolution,[],[f107])).
% 3.22/0.81  fof(f107,plain,(
% 3.22/0.81    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(equality_resolution,[],[f81])).
% 3.22/0.81  fof(f81,plain,(
% 3.22/0.81    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f45])).
% 3.22/0.81  fof(f1598,plain,(
% 3.22/0.81    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | ~spl12_79),
% 3.22/0.81    inference(avatar_component_clause,[],[f1596])).
% 3.22/0.81  fof(f1528,plain,(
% 3.22/0.81    spl12_2 | ~spl12_30),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f1527])).
% 3.22/0.81  fof(f1527,plain,(
% 3.22/0.81    $false | (spl12_2 | ~spl12_30)),
% 3.22/0.81    inference(subsumption_resolution,[],[f1526,f125])).
% 3.22/0.81  fof(f1526,plain,(
% 3.22/0.81    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | (spl12_2 | ~spl12_30)),
% 3.22/0.81    inference(forward_demodulation,[],[f118,f563])).
% 3.22/0.81  fof(f568,plain,(
% 3.22/0.81    spl12_30 | spl12_31 | ~spl12_1),
% 3.22/0.81    inference(avatar_split_clause,[],[f559,f112,f565,f561])).
% 3.22/0.81  fof(f559,plain,(
% 3.22/0.81    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | sK0 = sK1 | ~spl12_1),
% 3.22/0.81    inference(subsumption_resolution,[],[f555,f61])).
% 3.22/0.81  fof(f555,plain,(
% 3.22/0.81    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | sK0 = sK1 | ~v1_relat_1(sK2) | ~spl12_1),
% 3.22/0.81    inference(resolution,[],[f113,f105])).
% 3.22/0.81  fof(f113,plain,(
% 3.22/0.81    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl12_1),
% 3.22/0.81    inference(avatar_component_clause,[],[f112])).
% 3.22/0.81  fof(f120,plain,(
% 3.22/0.81    spl12_1 | spl12_2),
% 3.22/0.81    inference(avatar_split_clause,[],[f65,f116,f112])).
% 3.22/0.81  fof(f65,plain,(
% 3.22/0.81    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.22/0.81    inference(cnf_transformation,[],[f32])).
% 3.22/0.81  fof(f119,plain,(
% 3.22/0.81    ~spl12_1 | ~spl12_2),
% 3.22/0.81    inference(avatar_split_clause,[],[f66,f116,f112])).
% 3.22/0.81  fof(f66,plain,(
% 3.22/0.81    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.22/0.81    inference(cnf_transformation,[],[f32])).
% 3.22/0.81  % SZS output end Proof for theBenchmark
% 3.22/0.81  % (7939)------------------------------
% 3.22/0.81  % (7939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.81  % (7939)Termination reason: Refutation
% 3.22/0.81  
% 3.22/0.81  % (7939)Memory used [KB]: 12920
% 3.22/0.81  % (7939)Time elapsed: 0.410 s
% 3.22/0.81  % (7939)------------------------------
% 3.22/0.81  % (7939)------------------------------
% 3.22/0.83  % (7941)Time limit reached!
% 3.22/0.83  % (7941)------------------------------
% 3.22/0.83  % (7941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.83  % (7941)Termination reason: Time limit
% 3.22/0.83  
% 3.22/0.83  % (7941)Memory used [KB]: 8699
% 3.22/0.83  % (7941)Time elapsed: 0.428 s
% 3.22/0.83  % (7941)------------------------------
% 3.22/0.83  % (7941)------------------------------
% 3.22/0.83  % (7935)Success in time 0.482 s
%------------------------------------------------------------------------------
