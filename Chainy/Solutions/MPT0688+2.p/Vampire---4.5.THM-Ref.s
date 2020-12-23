%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0688+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   30 (  56 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 209 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1588,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1583,f1377])).

fof(f1377,plain,(
    r2_hidden(sK16(sK0,k2_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f1127,f1238])).

fof(f1238,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK16(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1121])).

fof(f1121,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK16(X0,X1),X1)
          & r2_hidden(sK16(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f1119,f1120])).

fof(f1120,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK16(X0,X1),X1)
        & r2_hidden(sK16(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1119,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1118])).

fof(f1118,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1067])).

fof(f1067,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1127,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1071])).

fof(f1071,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    & ! [X2] :
        ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
        | ~ r2_hidden(X2,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1003,f1070])).

fof(f1070,plain,
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

fof(f1003,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1002])).

fof(f1002,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f944])).

fof(f944,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f943])).

fof(f943,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f1583,plain,(
    ~ r2_hidden(sK16(sK0,k2_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f1421,f1378])).

fof(f1378,plain,(
    ~ r2_hidden(sK16(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f1127,f1239])).

fof(f1239,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK16(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1121])).

fof(f1421,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f1380,f1125])).

fof(f1125,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1071])).

fof(f1380,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1263,f1290])).

fof(f1290,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | sQ18_eqProxy(k1_xboole_0,k10_relat_1(X1,k1_tarski(X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f1174,f1262])).

fof(f1262,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f1174,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1088])).

fof(f1088,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1040])).

fof(f1040,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f942])).

fof(f942,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f1263,plain,(
    ! [X2] :
      ( ~ sQ18_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(X2)))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(equality_proxy_replacement,[],[f1126,f1262])).

fof(f1126,plain,(
    ! [X2] :
      ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f1071])).
%------------------------------------------------------------------------------
