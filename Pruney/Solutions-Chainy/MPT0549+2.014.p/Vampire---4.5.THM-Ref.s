%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 338 expanded)
%              Number of leaves         :   17 (  80 expanded)
%              Depth                    :   32
%              Number of atoms          :  327 (1435 expanded)
%              Number of equality atoms :   63 ( 308 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1630,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1629,f1469])).

fof(f1469,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f1462])).

fof(f1462,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f45,f1458])).

fof(f1458,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(resolution,[],[f1451,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f1451,plain,(
    ! [X4] : r1_xboole_0(k9_relat_1(sK1,sK0),X4) ),
    inference(resolution,[],[f1448,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1448,plain,(
    ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f1447,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f1447,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f1446])).

fof(f1446,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
      | ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1445,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f1445,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK1),sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f1444,f43])).

fof(f1444,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK1),sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f1441])).

fof(f1441,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK1),sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1440,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1440,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK1),k1_relat_1(sK1))
      | ~ r2_hidden(sK3(X0,X1,sK1),sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f1439,f43])).

fof(f1439,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK1),sK0)
      | ~ r2_hidden(sK3(X0,X1,sK1),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1438,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1438,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(k4_tarski(X36,X35),sK1)
      | ~ r2_hidden(X36,sK0)
      | ~ r2_hidden(X36,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f1437,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1437,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X36,sK0)
      | ~ r2_hidden(k4_tarski(X36,X35),sK1)
      | ~ r2_hidden(X36,k1_relat_1(sK1))
      | r1_xboole_0(k1_relat_1(sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f1436,f43])).

fof(f1436,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X36,sK0)
      | ~ r2_hidden(k4_tarski(X36,X35),sK1)
      | ~ r2_hidden(X36,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | r1_xboole_0(k1_relat_1(sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f1392,f76])).

fof(f76,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f54,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f1392,plain,(
    ! [X35,X36] :
      ( r2_hidden(X35,k1_xboole_0)
      | ~ r2_hidden(X36,sK0)
      | ~ r2_hidden(k4_tarski(X36,X35),sK1)
      | ~ r2_hidden(X36,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | r1_xboole_0(k1_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f68,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f45,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1629,plain,(
    r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f1628])).

fof(f1628,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f1623,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1623,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(k1_relat_1(sK1),X2),sK0)
      | r1_xboole_0(k1_relat_1(sK1),X2) ) ),
    inference(resolution,[],[f1618,f55])).

fof(f1618,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f1617,f76])).

fof(f1617,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(forward_demodulation,[],[f1616,f46])).

fof(f46,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1616,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f1607,f43])).

fof(f1607,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(X2,sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f71,f1588])).

fof(f1588,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f1587,f229])).

fof(f229,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f228,f50])).

fof(f50,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f228,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = k2_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f227,f48])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f227,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_xboole_0 = k2_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f153,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f153,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k2_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X1] :
      ( k1_xboole_0 = k2_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ) ),
    inference(superposition,[],[f138,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f138,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f133,f52])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k9_relat_1(X0,k1_xboole_0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f130,f55])).

fof(f130,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k9_relat_1(X5,k1_xboole_0))
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f67,f76])).

fof(f1587,plain,(
    r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1586,f73])).

fof(f1586,plain,(
    r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1567,f43])).

fof(f1567,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f99,f1458])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k9_relat_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f98,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k9_relat_1(X0,X1)))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f53,f59])).

fof(f53,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:06:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (27567)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (27574)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (27561)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (27575)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (27562)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (27566)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (27569)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (27562)Refutation not found, incomplete strategy% (27562)------------------------------
% 0.22/0.50  % (27562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27570)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (27562)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (27562)Memory used [KB]: 10618
% 0.22/0.50  % (27562)Time elapsed: 0.070 s
% 0.22/0.50  % (27562)------------------------------
% 0.22/0.50  % (27562)------------------------------
% 0.22/0.50  % (27568)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (27565)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (27564)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (27563)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (27576)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (27581)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (27578)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (27580)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (27581)Refutation not found, incomplete strategy% (27581)------------------------------
% 0.22/0.51  % (27581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27581)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27581)Memory used [KB]: 10618
% 0.22/0.51  % (27581)Time elapsed: 0.094 s
% 0.22/0.51  % (27581)------------------------------
% 0.22/0.51  % (27581)------------------------------
% 0.22/0.51  % (27579)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (27577)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (27572)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (27571)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (27564)Refutation not found, incomplete strategy% (27564)------------------------------
% 0.22/0.52  % (27564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27564)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27564)Memory used [KB]: 10618
% 0.22/0.52  % (27564)Time elapsed: 0.104 s
% 0.22/0.52  % (27564)------------------------------
% 0.22/0.52  % (27564)------------------------------
% 0.22/0.53  % (27573)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (27579)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f1630,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f1629,f1469])).
% 0.22/0.56  fof(f1469,plain,(
% 0.22/0.56    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f1462])).
% 0.22/0.56  fof(f1462,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f45,f1458])).
% 0.22/0.56  fof(f1458,plain,(
% 0.22/0.56    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f1451,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.56  fof(f1451,plain,(
% 0.22/0.56    ( ! [X4] : (r1_xboole_0(k9_relat_1(sK1,sK0),X4)) )),
% 0.22/0.56    inference(resolution,[],[f1448,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.56  fof(f1448,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK1,sK0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1447,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    v1_relat_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.56    inference(negated_conjecture,[],[f15])).
% 0.22/0.56  fof(f15,conjecture,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.22/0.56  fof(f1447,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f1446])).
% 0.22/0.56  fof(f1446,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK1,sK0)) | ~r2_hidden(X0,k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(resolution,[],[f1445,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(rectify,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.56  fof(f1445,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,sK1),sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1444,f43])).
% 0.22/0.56  fof(f1444,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,sK1),sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f1441])).
% 0.22/0.56  fof(f1441,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,sK1),sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(resolution,[],[f1440,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f1440,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,sK1),k1_relat_1(sK1)) | ~r2_hidden(sK3(X0,X1,sK1),sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1439,f43])).
% 0.22/0.56  fof(f1439,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,sK1),sK0) | ~r2_hidden(sK3(X0,X1,sK1),k1_relat_1(sK1)) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(resolution,[],[f1438,f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f1438,plain,(
% 0.22/0.56    ( ! [X35,X36] : (~r2_hidden(k4_tarski(X36,X35),sK1) | ~r2_hidden(X36,sK0) | ~r2_hidden(X36,k1_relat_1(sK1))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1437,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f1437,plain,(
% 0.22/0.56    ( ! [X35,X36] : (~r2_hidden(X36,sK0) | ~r2_hidden(k4_tarski(X36,X35),sK1) | ~r2_hidden(X36,k1_relat_1(sK1)) | r1_xboole_0(k1_relat_1(sK1),sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1436,f43])).
% 0.22/0.56  fof(f1436,plain,(
% 0.22/0.56    ( ! [X35,X36] : (~r2_hidden(X36,sK0) | ~r2_hidden(k4_tarski(X36,X35),sK1) | ~r2_hidden(X36,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1392,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(superposition,[],[f54,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.56  fof(f1392,plain,(
% 0.22/0.56    ( ! [X35,X36] : (r2_hidden(X35,k1_xboole_0) | ~r2_hidden(X36,sK0) | ~r2_hidden(k4_tarski(X36,X35),sK1) | ~r2_hidden(X36,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),sK0)) )),
% 0.22/0.56    inference(superposition,[],[f68,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    k1_xboole_0 = k9_relat_1(sK1,sK0) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    k1_xboole_0 != k9_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f1629,plain,(
% 0.22/0.56    r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f1628])).
% 0.22/0.56  fof(f1628,plain,(
% 0.22/0.56    r1_xboole_0(k1_relat_1(sK1),sK0) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.56    inference(resolution,[],[f1623,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f1623,plain,(
% 0.22/0.56    ( ! [X2] : (~r2_hidden(sK2(k1_relat_1(sK1),X2),sK0) | r1_xboole_0(k1_relat_1(sK1),X2)) )),
% 0.22/0.56    inference(resolution,[],[f1618,f55])).
% 0.22/0.56  fof(f1618,plain,(
% 0.22/0.56    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1617,f76])).
% 0.22/0.56  fof(f1617,plain,(
% 0.22/0.56    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f1616,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.56  fof(f1616,plain,(
% 0.22/0.56    ( ! [X2] : (r2_hidden(X2,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1607,f43])).
% 0.22/0.56  fof(f1607,plain,(
% 0.22/0.56    ( ! [X2] : (r2_hidden(X2,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(superposition,[],[f71,f1588])).
% 0.22/0.56  fof(f1588,plain,(
% 0.22/0.56    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f1587,f229])).
% 0.22/0.56  fof(f229,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(forward_demodulation,[],[f228,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = k2_relat_1(k6_relat_1(X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f227,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.56  fof(f227,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k2_relat_1(k6_relat_1(X0))) )),
% 0.22/0.56    inference(superposition,[],[f153,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_relat_1(X1) | k1_xboole_0 = k2_relat_1(X1)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f144])).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    ( ! [X1] : (k1_xboole_0 = k2_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),k1_xboole_0)) )),
% 0.22/0.56    inference(superposition,[],[f138,f103])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f100])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(superposition,[],[f59,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f133,f52])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_xboole_0(k9_relat_1(X0,k1_xboole_0),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f130,f55])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k9_relat_1(X5,k1_xboole_0)) | ~v1_relat_1(X5)) )),
% 0.22/0.56    inference(resolution,[],[f67,f76])).
% 0.22/0.56  fof(f1587,plain,(
% 0.22/0.56    r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)),
% 0.22/0.56    inference(forward_demodulation,[],[f1586,f73])).
% 0.22/0.56  fof(f1586,plain,(
% 0.22/0.56    r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1567,f43])).
% 0.22/0.56  fof(f1567,plain,(
% 0.22/0.56    r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0)) | ~v1_relat_1(sK1)),
% 0.22/0.56    inference(superposition,[],[f99,f1458])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k9_relat_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f98,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k9_relat_1(X0,X1))) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(superposition,[],[f53,f59])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(flattening,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (27579)------------------------------
% 0.22/0.56  % (27579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27579)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (27579)Memory used [KB]: 2174
% 0.22/0.56  % (27579)Time elapsed: 0.134 s
% 0.22/0.56  % (27579)------------------------------
% 0.22/0.56  % (27579)------------------------------
% 0.22/0.57  % (27560)Success in time 0.205 s
%------------------------------------------------------------------------------
