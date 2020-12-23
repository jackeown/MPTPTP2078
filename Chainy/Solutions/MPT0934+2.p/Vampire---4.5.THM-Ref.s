%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0934+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 104 expanded)
%              Number of leaves         :    7 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  156 ( 661 expanded)
%              Number of equality atoms :   49 ( 285 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2082,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2081,f1505])).

fof(f1505,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1478])).

fof(f1478,plain,
    ( sK1 != sK2
    & k2_mcart_1(sK1) = k2_mcart_1(sK2)
    & k1_mcart_1(sK1) = k1_mcart_1(sK2)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0)
    & v1_relat_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1423,f1477,f1476,f1475])).

fof(f1475,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_mcart_1(X2) = k2_mcart_1(X1)
                & k1_mcart_1(X2) = k1_mcart_1(X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,X0) )
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,sK0) )
      & v1_relat_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1476,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k2_mcart_1(X2) = k2_mcart_1(X1)
            & k1_mcart_1(X2) = k1_mcart_1(X1)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,sK0) )
   => ( ? [X2] :
          ( sK1 != X2
          & k2_mcart_1(X2) = k2_mcart_1(sK1)
          & k1_mcart_1(X2) = k1_mcart_1(sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1477,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k2_mcart_1(X2) = k2_mcart_1(sK1)
        & k1_mcart_1(X2) = k1_mcart_1(sK1)
        & m1_subset_1(X2,sK0) )
   => ( sK1 != sK2
      & k2_mcart_1(sK1) = k2_mcart_1(sK2)
      & k1_mcart_1(sK1) = k1_mcart_1(sK2)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1423,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1422])).

fof(f1422,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1415])).

fof(f1415,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ( k2_mcart_1(X2) = k2_mcart_1(X1)
                    & k1_mcart_1(X2) = k1_mcart_1(X1) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1414])).

fof(f1414,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ( k2_mcart_1(X2) = k2_mcart_1(X1)
                  & k1_mcart_1(X2) = k1_mcart_1(X1) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_mcart_1)).

fof(f2081,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f2079,f1675])).

fof(f1675,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1672,f1504])).

fof(f1504,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f1478])).

fof(f1672,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f1506,f1569])).

fof(f1569,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1495])).

fof(f1495,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1462])).

fof(f1462,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1506,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f1478])).

fof(f2079,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1683,f1679])).

fof(f1679,plain,(
    r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f1676,f1504])).

fof(f1676,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f1507,f1569])).

fof(f1507,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f1478])).

fof(f1683,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1682,f1609])).

fof(f1609,plain,(
    sQ14_eqProxy(k1_mcart_1(sK1),k1_mcart_1(sK2)) ),
    inference(equality_proxy_replacement,[],[f1508,f1606])).

fof(f1606,plain,(
    ! [X1,X0] :
      ( sQ14_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ14_eqProxy])])).

fof(f1508,plain,(
    k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f1478])).

fof(f1682,plain,(
    ! [X0] :
      ( ~ sQ14_eqProxy(k1_mcart_1(sK1),k1_mcart_1(sK2))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1681,f1608])).

fof(f1608,plain,(
    sQ14_eqProxy(k2_mcart_1(sK1),k2_mcart_1(sK2)) ),
    inference(equality_proxy_replacement,[],[f1509,f1606])).

fof(f1509,plain,(
    k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f1478])).

fof(f1681,plain,(
    ! [X0] :
      ( ~ sQ14_eqProxy(k2_mcart_1(sK1),k2_mcart_1(sK2))
      | ~ sQ14_eqProxy(k1_mcart_1(sK1),k1_mcart_1(sK2))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f1607,f1629])).

fof(f1629,plain,(
    ! [X2,X0,X1] :
      ( sQ14_eqProxy(X0,X2)
      | ~ sQ14_eqProxy(k2_mcart_1(X0),k2_mcart_1(X2))
      | ~ sQ14_eqProxy(k1_mcart_1(X0),k1_mcart_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f1537,f1606,f1606,f1606])).

fof(f1537,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | k2_mcart_1(X0) != k2_mcart_1(X2)
      | k1_mcart_1(X0) != k1_mcart_1(X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1440])).

fof(f1440,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X0) != k2_mcart_1(X2)
          | k1_mcart_1(X0) != k1_mcart_1(X2)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1439])).

fof(f1439,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X0) != k2_mcart_1(X2)
          | k1_mcart_1(X0) != k1_mcart_1(X2)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1413])).

fof(f1413,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_mcart_1)).

fof(f1607,plain,(
    ~ sQ14_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f1510,f1606])).

fof(f1510,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f1478])).
%------------------------------------------------------------------------------
