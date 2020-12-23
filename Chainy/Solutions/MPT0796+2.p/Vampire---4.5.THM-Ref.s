%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0796+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   28 (  39 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 121 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2215,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2214,f1594])).

fof(f1594,plain,(
    v1_relat_1(sK20) ),
    inference(cnf_transformation,[],[f1405])).

fof(f1405,plain,
    ( ~ r4_wellord1(sK20,sK20)
    & v1_relat_1(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f1196,f1404])).

fof(f1404,plain,
    ( ? [X0] :
        ( ~ r4_wellord1(X0,X0)
        & v1_relat_1(X0) )
   => ( ~ r4_wellord1(sK20,sK20)
      & v1_relat_1(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f1196,plain,(
    ? [X0] :
      ( ~ r4_wellord1(X0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1187])).

fof(f1187,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r4_wellord1(X0,X0) ) ),
    inference(negated_conjecture,[],[f1186])).

fof(f1186,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r4_wellord1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_wellord1)).

fof(f2214,plain,(
    ~ v1_relat_1(sK20) ),
    inference(subsumption_resolution,[],[f2213,f1896])).

fof(f1896,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f2213,plain,
    ( ~ v1_relat_1(k6_relat_1(k3_relat_1(sK20)))
    | ~ v1_relat_1(sK20) ),
    inference(subsumption_resolution,[],[f2212,f1893])).

fof(f1893,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f921])).

fof(f921,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f2212,plain,
    ( ~ v1_funct_1(k6_relat_1(k3_relat_1(sK20)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK20)))
    | ~ v1_relat_1(sK20) ),
    inference(subsumption_resolution,[],[f2203,f1595])).

fof(f1595,plain,(
    ~ r4_wellord1(sK20,sK20) ),
    inference(cnf_transformation,[],[f1405])).

fof(f2203,plain,
    ( r4_wellord1(sK20,sK20)
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK20)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK20)))
    | ~ v1_relat_1(sK20) ),
    inference(duplicate_literal_removal,[],[f2199])).

fof(f2199,plain,
    ( r4_wellord1(sK20,sK20)
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK20)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK20)))
    | ~ v1_relat_1(sK20)
    | ~ v1_relat_1(sK20) ),
    inference(resolution,[],[f1952,f1599])).

fof(f1599,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1409])).

fof(f1409,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ( r3_wellord1(X0,X1,sK21(X0,X1))
                & v1_funct_1(sK21(X0,X1))
                & v1_relat_1(sK21(X0,X1)) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f1407,f1408])).

fof(f1408,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK21(X0,X1))
        & v1_funct_1(sK21(X0,X1))
        & v1_relat_1(sK21(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1407,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X3] :
                  ( r3_wellord1(X0,X1,X3)
                  & v1_funct_1(X3)
                  & v1_relat_1(X3) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1406])).

fof(f1406,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X2] :
                  ( r3_wellord1(X0,X1,X2)
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1197])).

fof(f1197,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1138])).

fof(f1138,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(f1952,plain,(
    r3_wellord1(sK20,sK20,k6_relat_1(k3_relat_1(sK20))) ),
    inference(resolution,[],[f1594,f1618])).

fof(f1618,plain,(
    ! [X0] :
      ( r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1202])).

fof(f1202,plain,(
    ! [X0] :
      ( r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1185])).

fof(f1185,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_wellord1)).
%------------------------------------------------------------------------------
