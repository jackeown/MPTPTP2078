%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0682+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 14.58s
% Output     : Refutation 15.04s
% Verified   : 
% Statistics : Number of formulae       :   48 (  83 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 254 expanded)
%              Number of equality atoms :   56 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20152,f2676])).

fof(f2676,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f2675])).

fof(f2675,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f2049])).

fof(f2049,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1618])).

fof(f1618,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK40(X0,X1) != X0
            | ~ r2_hidden(sK40(X0,X1),X1) )
          & ( sK40(X0,X1) = X0
            | r2_hidden(sK40(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK40])],[f1616,f1617])).

fof(f1617,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK40(X0,X1) != X0
          | ~ r2_hidden(sK40(X0,X1),X1) )
        & ( sK40(X0,X1) = X0
          | r2_hidden(sK40(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1616,plain,(
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
    inference(rectify,[],[f1615])).

fof(f1615,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f20152,plain,(
    ~ r2_hidden(k3_xboole_0(sK12,k9_relat_1(sK14,sK13)),k1_tarski(k3_xboole_0(sK12,k9_relat_1(sK14,sK13)))) ),
    inference(forward_demodulation,[],[f20112,f1888])).

fof(f1888,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f20112,plain,(
    ~ r2_hidden(k3_xboole_0(sK12,k9_relat_1(sK14,sK13)),k1_tarski(k3_xboole_0(k9_relat_1(sK14,sK13),sK12))) ),
    inference(backward_demodulation,[],[f3530,f20093])).

fof(f20093,plain,(
    ! [X0,X1] : k9_relat_1(k8_relat_1(X0,sK14),X1) = k3_xboole_0(k9_relat_1(sK14,X1),X0) ),
    inference(backward_demodulation,[],[f7859,f20075])).

fof(f20075,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k8_relat_1(X0,sK14),X1)) = k3_xboole_0(k9_relat_1(sK14,X1),X0) ),
    inference(backward_demodulation,[],[f9802,f20025])).

fof(f20025,plain,(
    ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK14),X1) = k8_relat_1(X0,k7_relat_1(sK14,X1)) ),
    inference(unit_resulting_resolution,[],[f1852,f1954])).

fof(f1954,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f1077])).

fof(f1077,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f744])).

fof(f744,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f1852,plain,(
    v1_relat_1(sK14) ),
    inference(cnf_transformation,[],[f1536])).

fof(f1536,plain,
    ( k9_relat_1(k8_relat_1(sK12,sK14),sK13) != k3_xboole_0(sK12,k9_relat_1(sK14,sK13))
    & v1_funct_1(sK14)
    & v1_relat_1(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f1002,f1535])).

fof(f1535,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK12,sK14),sK13) != k3_xboole_0(sK12,k9_relat_1(sK14,sK13))
      & v1_funct_1(sK14)
      & v1_relat_1(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f1002,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1001])).

fof(f1001,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f935])).

fof(f935,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f934])).

fof(f934,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

fof(f9802,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK14,X1))) = k3_xboole_0(k9_relat_1(sK14,X1),X0) ),
    inference(forward_demodulation,[],[f9748,f7865])).

fof(f7865,plain,(
    ! [X0] : k9_relat_1(sK14,X0) = k2_relat_1(k7_relat_1(sK14,X0)) ),
    inference(unit_resulting_resolution,[],[f1852,f1914])).

fof(f1914,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f1049])).

fof(f1049,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f750,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f9748,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK14,X1))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK14,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f2985,f1988])).

fof(f1988,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f1100])).

fof(f1100,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f722])).

fof(f722,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f2985,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK14,X0)) ),
    inference(unit_resulting_resolution,[],[f1852,f2489])).

fof(f2489,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1387])).

fof(f1387,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f669])).

fof(f669,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f7859,plain,(
    ! [X0,X1] : k9_relat_1(k8_relat_1(X0,sK14),X1) = k2_relat_1(k7_relat_1(k8_relat_1(X0,sK14),X1)) ),
    inference(unit_resulting_resolution,[],[f2915,f1914])).

fof(f2915,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK14)) ),
    inference(unit_resulting_resolution,[],[f1852,f1994])).

fof(f1994,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1106])).

fof(f1106,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f670])).

fof(f670,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f3530,plain,(
    ~ r2_hidden(k3_xboole_0(sK12,k9_relat_1(sK14,sK13)),k1_tarski(k9_relat_1(k8_relat_1(sK12,sK14),sK13))) ),
    inference(unit_resulting_resolution,[],[f1854,f2677])).

fof(f2677,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f2048])).

fof(f2048,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1618])).

fof(f1854,plain,(
    k9_relat_1(k8_relat_1(sK12,sK14),sK13) != k3_xboole_0(sK12,k9_relat_1(sK14,sK13)) ),
    inference(cnf_transformation,[],[f1536])).
%------------------------------------------------------------------------------
