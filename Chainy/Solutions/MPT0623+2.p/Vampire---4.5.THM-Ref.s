%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0623+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 112 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   20
%              Number of atoms          :  222 ( 481 expanded)
%              Number of equality atoms :   81 ( 204 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3317,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3296,f2237])).

fof(f2237,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f3296,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK28(sK38(k1_xboole_0))),k1_xboole_0) ),
    inference(resolution,[],[f3151,f2228])).

fof(f2228,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f1203])).

fof(f1203,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f304])).

fof(f304,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f3151,plain,(
    r2_hidden(sK28(sK38(k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3150,f2123])).

fof(f2123,plain,(
    ! [X0] : k1_relat_1(sK38(X0)) = X0 ),
    inference(cnf_transformation,[],[f1571])).

fof(f1571,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK38(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK38(X0)) = X0
      & v1_funct_1(sK38(X0))
      & v1_relat_1(sK38(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK38])],[f1150,f1570])).

fof(f1570,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK38(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK38(X0)) = X0
        & v1_funct_1(sK38(X0))
        & v1_relat_1(sK38(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1150,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f897])).

fof(f897,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f3150,plain,(
    r2_hidden(sK28(sK38(k1_xboole_0)),k1_relat_1(sK38(k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f3117,f2121])).

fof(f2121,plain,(
    ! [X0] : v1_relat_1(sK38(X0)) ),
    inference(cnf_transformation,[],[f1571])).

fof(f3117,plain,
    ( r2_hidden(sK28(sK38(k1_xboole_0)),k1_relat_1(sK38(k1_xboole_0)))
    | ~ v1_relat_1(sK38(k1_xboole_0)) ),
    inference(resolution,[],[f3081,f2015])).

fof(f2015,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | r2_hidden(sK28(X1),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1539])).

fof(f1539,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK28(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28])],[f1057,f1538])).

fof(f1538,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK28(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f1057,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1056])).

fof(f1056,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f803])).

fof(f803,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f3081,plain,(
    r2_hidden(sK18(k2_relat_1(sK38(k1_xboole_0)),sK7),k2_relat_1(sK38(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f2994,f3070])).

fof(f3070,plain,(
    k1_xboole_0 = sK8 ),
    inference(subsumption_resolution,[],[f3044,f1833])).

fof(f1833,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 = sK8 ),
    inference(cnf_transformation,[],[f1477])).

fof(f1477,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK7)
        | k1_relat_1(X2) != sK8
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK8
      | k1_xboole_0 != sK7 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f916,f1476])).

fof(f1476,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK7)
          | k1_relat_1(X2) != sK8
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK8
        | k1_xboole_0 != sK7 ) ) ),
    introduced(choice_axiom,[])).

fof(f916,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f915])).

fof(f915,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f906])).

fof(f906,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f905])).

fof(f905,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f3044,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(resolution,[],[f3007,f2240])).

fof(f2240,plain,(
    ! [X0] :
      ( r2_hidden(sK63(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1635])).

fof(f1635,plain,(
    ! [X0] :
      ( r2_hidden(sK63(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK63])],[f1207,f1634])).

fof(f1634,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK63(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1207,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f3007,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | k1_xboole_0 = sK8 ) ),
    inference(resolution,[],[f3005,f1922])).

fof(f1922,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1499])).

fof(f1499,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f3005,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK7)
      | k1_xboole_0 = sK8 ) ),
    inference(duplicate_literal_removal,[],[f3004])).

fof(f3004,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK7)
      | k1_xboole_0 = sK8
      | k1_xboole_0 = sK8 ) ),
    inference(superposition,[],[f3002,f2035])).

fof(f2035,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK29(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1542])).

fof(f1542,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK29(X0,X1))
          & k1_relat_1(sK29(X0,X1)) = X0
          & v1_funct_1(sK29(X0,X1))
          & v1_relat_1(sK29(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29])],[f1078,f1541])).

fof(f1541,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK29(X0,X1))
        & k1_relat_1(sK29(X0,X1)) = X0
        & v1_funct_1(sK29(X0,X1))
        & v1_relat_1(sK29(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1078,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f902])).

fof(f902,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f3002,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK29(sK8,X0)),sK7)
      | k1_xboole_0 = sK8 ) ),
    inference(equality_resolution,[],[f2984])).

fof(f2984,plain,(
    ! [X4,X3] :
      ( sK8 != X3
      | ~ r1_tarski(k2_relat_1(sK29(X3,X4)),sK7)
      | k1_xboole_0 = X3 ) ),
    inference(subsumption_resolution,[],[f2983,f2032])).

fof(f2032,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK29(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1542])).

fof(f2983,plain,(
    ! [X4,X3] :
      ( sK8 != X3
      | ~ r1_tarski(k2_relat_1(sK29(X3,X4)),sK7)
      | ~ v1_relat_1(sK29(X3,X4))
      | k1_xboole_0 = X3 ) ),
    inference(subsumption_resolution,[],[f2973,f2033])).

fof(f2033,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK29(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1542])).

fof(f2973,plain,(
    ! [X4,X3] :
      ( sK8 != X3
      | ~ r1_tarski(k2_relat_1(sK29(X3,X4)),sK7)
      | ~ v1_funct_1(sK29(X3,X4))
      | ~ v1_relat_1(sK29(X3,X4))
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f1834,f2034])).

fof(f2034,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK29(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1542])).

fof(f1834,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK8
      | ~ r1_tarski(k2_relat_1(X2),sK7)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1477])).

fof(f2994,plain,(
    r2_hidden(sK18(k2_relat_1(sK38(sK8)),sK7),k2_relat_1(sK38(sK8))) ),
    inference(resolution,[],[f2993,f1936])).

fof(f1936,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK18(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1512])).

fof(f1512,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK18(X0,X1),X1)
          & r2_hidden(sK18(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f1510,f1511])).

fof(f1511,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1510,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1509])).

fof(f1509,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f998])).

fof(f998,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f2993,plain,(
    ~ r1_tarski(k2_relat_1(sK38(sK8)),sK7) ),
    inference(equality_resolution,[],[f2988])).

fof(f2988,plain,(
    ! [X7] :
      ( sK8 != X7
      | ~ r1_tarski(k2_relat_1(sK38(X7)),sK7) ) ),
    inference(subsumption_resolution,[],[f2987,f2121])).

fof(f2987,plain,(
    ! [X7] :
      ( sK8 != X7
      | ~ r1_tarski(k2_relat_1(sK38(X7)),sK7)
      | ~ v1_relat_1(sK38(X7)) ) ),
    inference(subsumption_resolution,[],[f2975,f2122])).

fof(f2122,plain,(
    ! [X0] : v1_funct_1(sK38(X0)) ),
    inference(cnf_transformation,[],[f1571])).

fof(f2975,plain,(
    ! [X7] :
      ( sK8 != X7
      | ~ r1_tarski(k2_relat_1(sK38(X7)),sK7)
      | ~ v1_funct_1(sK38(X7))
      | ~ v1_relat_1(sK38(X7)) ) ),
    inference(superposition,[],[f1834,f2123])).
%------------------------------------------------------------------------------
