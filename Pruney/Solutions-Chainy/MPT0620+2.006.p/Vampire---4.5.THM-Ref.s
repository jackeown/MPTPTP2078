%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:54 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 905 expanded)
%              Number of leaves         :    8 ( 221 expanded)
%              Depth                    :   26
%              Number of atoms          :  224 (3163 expanded)
%              Number of equality atoms :   96 (1341 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1490,plain,(
    $false ),
    inference(global_subsumption,[],[f120,f1489])).

fof(f1489,plain,(
    ! [X0] : sP3(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1438,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f35,f37,f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f37,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f1438,plain,(
    ! [X0] : sP3(X0,sK6(k1_xboole_0,X0)) ),
    inference(superposition,[],[f197,f1408])).

fof(f1408,plain,(
    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1406,f867])).

fof(f867,plain,(
    ! [X2,X0,X1] : sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),X1)),X2),X2) = X1 ),
    inference(unit_resulting_resolution,[],[f498,f316])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,sK6(X2,X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | ~ sP3(X1,sK6(X2,X0))
      | ~ sP3(X1,sK6(X2,X0)) ) ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK4(sK6(X1,X2),X3),X1)
      | ~ sP3(X3,sK6(X1,X2)) ) ),
    inference(superposition,[],[f25,f37])).

fof(f25,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f69,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(sK6(X3,X4),X5),X3)
      | X4 = X5
      | ~ sP3(X5,sK6(X3,X4)) ) ),
    inference(superposition,[],[f34,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f498,plain,(
    ! [X2,X0,X1] : sP3(sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),X1)),X2),X2),sK6(k2_relat_1(sK6(sK0,X0)),X1)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f224,f245])).

fof(f245,plain,(
    ! [X10,X11,X9] :
      ( sP3(sK4(sK6(k2_relat_1(X10),X11),X9),X10)
      | ~ v1_funct_1(X10)
      | ~ sP3(X9,sK6(k2_relat_1(X10),X11))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f224,plain,(
    ! [X2,X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X0)) ),
    inference(unit_resulting_resolution,[],[f206,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f70,f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f44,f34])).

fof(f44,plain,(
    ! [X0,X3] :
      ( sP3(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f206,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X0))) ),
    inference(unit_resulting_resolution,[],[f35,f36,f197,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP3(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f1406,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_relat_1(sK6(sK0,sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),sK1)),X1),X1))) ),
    inference(unit_resulting_resolution,[],[f867,f36,f35,f1395])).

fof(f1395,plain,(
    ! [X9] :
      ( sK1 != X9
      | k1_xboole_0 = k2_relat_1(sK6(sK0,X9))
      | ~ v1_relat_1(sK6(sK0,X9))
      | ~ v1_funct_1(sK6(sK0,X9)) ) ),
    inference(global_subsumption,[],[f45,f1389])).

fof(f1389,plain,(
    ! [X9] :
      ( sK1 != X9
      | k1_xboole_0 = k2_relat_1(sK6(sK0,X9))
      | k1_enumset1(sK1,sK1,sK1) = k2_relat_1(sK6(sK0,X9))
      | ~ v1_relat_1(sK6(sK0,X9))
      | ~ v1_funct_1(sK6(sK0,X9)) ) ),
    inference(duplicate_literal_removal,[],[f1388])).

fof(f1388,plain,(
    ! [X9] :
      ( sK1 != X9
      | k1_xboole_0 = k2_relat_1(sK6(sK0,X9))
      | k1_enumset1(sK1,sK1,sK1) = k2_relat_1(sK6(sK0,X9))
      | k1_xboole_0 = k2_relat_1(sK6(sK0,X9))
      | ~ v1_relat_1(sK6(sK0,X9))
      | ~ v1_funct_1(sK6(sK0,X9)) ) ),
    inference(superposition,[],[f40,f1369])).

fof(f1369,plain,(
    ! [X1] :
      ( sK5(k2_relat_1(sK6(sK0,X1)),sK1) = X1
      | k1_xboole_0 = k2_relat_1(sK6(sK0,X1))
      | ~ v1_relat_1(sK6(sK0,X1))
      | ~ v1_funct_1(sK6(sK0,X1)) ) ),
    inference(resolution,[],[f816,f316])).

fof(f816,plain,(
    ! [X2] :
      ( sP3(sK5(k2_relat_1(sK6(sK0,X2)),sK1),sK6(sK0,X2))
      | ~ v1_funct_1(sK6(sK0,X2))
      | k1_xboole_0 = k2_relat_1(sK6(sK0,X2))
      | ~ v1_relat_1(sK6(sK0,X2)) ) ),
    inference(resolution,[],[f721,f42])).

fof(f721,plain,(
    ! [X5] :
      ( r2_hidden(sK5(k2_relat_1(sK6(sK0,X5)),sK1),k2_relat_1(sK6(sK0,X5)))
      | k1_xboole_0 = k2_relat_1(sK6(sK0,X5)) ) ),
    inference(resolution,[],[f446,f185])).

fof(f185,plain,(
    ! [X0] : sP3(X0,sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f178,f73])).

fof(f178,plain,(
    r2_hidden(sK2(k1_xboole_0,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f18,f176])).

fof(f176,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_xboole_0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(global_subsumption,[],[f52,f53,f175])).

fof(f175,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0,X1),X1) ) ),
    inference(forward_demodulation,[],[f170,f20])).

fof(f20,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f170,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0,X1),X1)
      | k2_relat_1(k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f29,f120])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sP3(sK2(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f35,f46])).

fof(f52,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f36,f46])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f446,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(k2_relat_1(sK6(sK0,X1)),sK6(X2,X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,sK1),X0) ) ),
    inference(superposition,[],[f399,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f399,plain,(
    ! [X0,X1] : ~ sP3(k2_relat_1(sK6(sK0,X0)),sK6(X1,k1_enumset1(sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f45,f316])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0] : k1_enumset1(sK1,sK1,sK1) != k2_relat_1(sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f39])).

fof(f39,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_enumset1(sK1,sK1,sK1)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f17,f38])).

fof(f17,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | k2_relat_1(X2) != k1_tarski(sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f197,plain,(
    ! [X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(sK0,X1)),X0)) ),
    inference(unit_resulting_resolution,[],[f188,f73])).

fof(f188,plain,(
    ! [X0] : r2_hidden(X0,k2_relat_1(sK6(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f35,f36,f185,f43])).

fof(f120,plain,(
    ! [X0] : ~ sP3(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f117,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0)
      | ~ sP3(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f25,f19])).

fof(f19,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f117,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f37,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_enumset1(sK1,sK1,sK1) != X1
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_enumset1(sK1,sK1,sK1) != X1
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f91,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k1_xboole_0,X1) = X0
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f34,f46])).

fof(f91,plain,(
    ! [X1] :
      ( k1_enumset1(sK1,sK1,sK1) != k1_funct_1(k1_xboole_0,X1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f45,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:21:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (26939)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.49  % (26947)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.50  % (26947)Refutation not found, incomplete strategy% (26947)------------------------------
% 0.22/0.50  % (26947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26947)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26947)Memory used [KB]: 10746
% 0.22/0.50  % (26947)Time elapsed: 0.088 s
% 0.22/0.50  % (26947)------------------------------
% 0.22/0.50  % (26947)------------------------------
% 0.22/0.51  % (26927)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (26924)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (26928)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (26922)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (26928)Refutation not found, incomplete strategy% (26928)------------------------------
% 0.22/0.52  % (26928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26928)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (26928)Memory used [KB]: 10618
% 0.22/0.52  % (26928)Time elapsed: 0.107 s
% 0.22/0.52  % (26928)------------------------------
% 0.22/0.52  % (26928)------------------------------
% 0.22/0.52  % (26932)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (26925)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (26929)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (26923)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (26940)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (26920)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.53  % (26950)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.53  % (26949)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (26924)Refutation not found, incomplete strategy% (26924)------------------------------
% 1.35/0.54  % (26924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26924)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (26924)Memory used [KB]: 6140
% 1.35/0.54  % (26924)Time elapsed: 0.130 s
% 1.35/0.54  % (26924)------------------------------
% 1.35/0.54  % (26924)------------------------------
% 1.35/0.54  % (26944)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (26921)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.54  % (26942)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.54  % (26943)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.54  % (26942)Refutation not found, incomplete strategy% (26942)------------------------------
% 1.35/0.54  % (26942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26942)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (26942)Memory used [KB]: 1663
% 1.35/0.54  % (26942)Time elapsed: 0.133 s
% 1.35/0.54  % (26942)------------------------------
% 1.35/0.54  % (26942)------------------------------
% 1.35/0.54  % (26943)Refutation not found, incomplete strategy% (26943)------------------------------
% 1.35/0.54  % (26943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26933)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.54  % (26943)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (26943)Memory used [KB]: 10618
% 1.35/0.54  % (26943)Time elapsed: 0.098 s
% 1.35/0.54  % (26943)------------------------------
% 1.35/0.54  % (26943)------------------------------
% 1.35/0.54  % (26922)Refutation not found, incomplete strategy% (26922)------------------------------
% 1.35/0.54  % (26922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26922)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (26922)Memory used [KB]: 10618
% 1.35/0.54  % (26922)Time elapsed: 0.123 s
% 1.35/0.54  % (26922)------------------------------
% 1.35/0.54  % (26922)------------------------------
% 1.35/0.54  % (26941)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.54  % (26930)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.54  % (26945)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (26930)Refutation not found, incomplete strategy% (26930)------------------------------
% 1.35/0.54  % (26930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26930)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (26930)Memory used [KB]: 10618
% 1.35/0.54  % (26930)Time elapsed: 0.130 s
% 1.35/0.54  % (26930)------------------------------
% 1.35/0.54  % (26930)------------------------------
% 1.35/0.54  % (26931)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (26938)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.54  % (26941)Refutation not found, incomplete strategy% (26941)------------------------------
% 1.35/0.54  % (26941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26941)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (26941)Memory used [KB]: 10618
% 1.35/0.54  % (26941)Time elapsed: 0.131 s
% 1.35/0.54  % (26941)------------------------------
% 1.35/0.54  % (26941)------------------------------
% 1.35/0.54  % (26938)Refutation not found, incomplete strategy% (26938)------------------------------
% 1.35/0.54  % (26938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26938)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (26938)Memory used [KB]: 10618
% 1.35/0.54  % (26938)Time elapsed: 0.131 s
% 1.35/0.54  % (26938)------------------------------
% 1.35/0.54  % (26938)------------------------------
% 1.35/0.55  % (26936)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.55  % (26946)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.55  % (26946)Refutation not found, incomplete strategy% (26946)------------------------------
% 1.35/0.55  % (26946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (26946)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (26946)Memory used [KB]: 6268
% 1.35/0.55  % (26946)Time elapsed: 0.141 s
% 1.35/0.55  % (26946)------------------------------
% 1.35/0.55  % (26946)------------------------------
% 1.53/0.55  % (26934)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.55  % (26948)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.56  % (26926)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.57  % (26931)Refutation not found, incomplete strategy% (26931)------------------------------
% 1.53/0.57  % (26931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (26931)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (26931)Memory used [KB]: 10618
% 1.53/0.57  % (26931)Time elapsed: 0.161 s
% 1.53/0.57  % (26931)------------------------------
% 1.53/0.57  % (26931)------------------------------
% 1.53/0.57  % (26937)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.61  % (26951)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.96/0.65  % (26945)Refutation found. Thanks to Tanya!
% 1.96/0.65  % SZS status Theorem for theBenchmark
% 1.96/0.65  % SZS output start Proof for theBenchmark
% 1.96/0.65  fof(f1490,plain,(
% 1.96/0.65    $false),
% 1.96/0.65    inference(global_subsumption,[],[f120,f1489])).
% 1.96/0.65  fof(f1489,plain,(
% 1.96/0.65    ( ! [X0] : (sP3(X0,k1_xboole_0)) )),
% 1.96/0.65    inference(forward_demodulation,[],[f1438,f46])).
% 1.96/0.65  fof(f46,plain,(
% 1.96/0.65    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f35,f37,f22])).
% 1.96/0.65  fof(f22,plain,(
% 1.96/0.65    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.96/0.65    inference(cnf_transformation,[],[f12])).
% 1.96/0.65  fof(f12,plain,(
% 1.96/0.65    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.96/0.65    inference(flattening,[],[f11])).
% 1.96/0.65  fof(f11,plain,(
% 1.96/0.65    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.96/0.65    inference(ennf_transformation,[],[f5])).
% 1.96/0.65  fof(f5,axiom,(
% 1.96/0.65    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.96/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.96/0.65  fof(f37,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.96/0.65    inference(cnf_transformation,[],[f16])).
% 1.96/0.65  fof(f16,plain,(
% 1.96/0.65    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.96/0.65    inference(ennf_transformation,[],[f7])).
% 1.96/0.65  fof(f7,axiom,(
% 1.96/0.65    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.96/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.96/0.65  fof(f35,plain,(
% 1.96/0.65    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.96/0.65    inference(cnf_transformation,[],[f16])).
% 1.96/0.65  fof(f1438,plain,(
% 1.96/0.65    ( ! [X0] : (sP3(X0,sK6(k1_xboole_0,X0))) )),
% 1.96/0.65    inference(superposition,[],[f197,f1408])).
% 1.96/0.65  fof(f1408,plain,(
% 1.96/0.65    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1))),
% 1.96/0.65    inference(forward_demodulation,[],[f1406,f867])).
% 1.96/0.65  fof(f867,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),X1)),X2),X2) = X1) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f498,f316])).
% 1.96/0.65  fof(f316,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (~sP3(X1,sK6(X2,X0)) | X0 = X1) )),
% 1.96/0.65    inference(duplicate_literal_removal,[],[f309])).
% 1.96/0.65  fof(f309,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (X0 = X1 | ~sP3(X1,sK6(X2,X0)) | ~sP3(X1,sK6(X2,X0))) )),
% 1.96/0.65    inference(resolution,[],[f69,f57])).
% 1.96/0.65  fof(f57,plain,(
% 1.96/0.65    ( ! [X2,X3,X1] : (r2_hidden(sK4(sK6(X1,X2),X3),X1) | ~sP3(X3,sK6(X1,X2))) )),
% 1.96/0.65    inference(superposition,[],[f25,f37])).
% 1.96/0.65  fof(f25,plain,(
% 1.96/0.65    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f14])).
% 1.96/0.65  fof(f14,plain,(
% 1.96/0.65    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.96/0.65    inference(flattening,[],[f13])).
% 1.96/0.65  fof(f13,plain,(
% 1.96/0.65    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.96/0.65    inference(ennf_transformation,[],[f6])).
% 1.96/0.65  fof(f6,axiom,(
% 1.96/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.96/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.96/0.65  fof(f69,plain,(
% 1.96/0.65    ( ! [X4,X5,X3] : (~r2_hidden(sK4(sK6(X3,X4),X5),X3) | X4 = X5 | ~sP3(X5,sK6(X3,X4))) )),
% 1.96/0.65    inference(superposition,[],[f34,f26])).
% 1.96/0.65  fof(f26,plain,(
% 1.96/0.65    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f14])).
% 1.96/0.65  fof(f34,plain,(
% 1.96/0.65    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f16])).
% 1.96/0.65  fof(f498,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (sP3(sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),X1)),X2),X2),sK6(k2_relat_1(sK6(sK0,X0)),X1))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f35,f36,f224,f245])).
% 1.96/0.65  fof(f245,plain,(
% 1.96/0.65    ( ! [X10,X11,X9] : (sP3(sK4(sK6(k2_relat_1(X10),X11),X9),X10) | ~v1_funct_1(X10) | ~sP3(X9,sK6(k2_relat_1(X10),X11)) | ~v1_relat_1(X10)) )),
% 1.96/0.65    inference(resolution,[],[f57,f42])).
% 1.96/0.65  fof(f42,plain,(
% 1.96/0.65    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 1.96/0.65    inference(equality_resolution,[],[f28])).
% 1.96/0.65  fof(f28,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.96/0.65    inference(cnf_transformation,[],[f14])).
% 1.96/0.65  fof(f224,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X0))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f206,f73])).
% 1.96/0.65  fof(f73,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.96/0.65    inference(duplicate_literal_removal,[],[f72])).
% 1.96/0.65  fof(f72,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.96/0.65    inference(forward_demodulation,[],[f70,f37])).
% 1.96/0.65  fof(f70,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.96/0.65    inference(superposition,[],[f44,f34])).
% 1.96/0.65  fof(f44,plain,(
% 1.96/0.65    ( ! [X0,X3] : (sP3(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.96/0.65    inference(equality_resolution,[],[f24])).
% 1.96/0.65  fof(f24,plain,(
% 1.96/0.65    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP3(X2,X0)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f14])).
% 1.96/0.65  fof(f206,plain,(
% 1.96/0.65    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X0)))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f35,f36,f197,f43])).
% 1.96/0.65  fof(f43,plain,(
% 1.96/0.65    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 1.96/0.65    inference(equality_resolution,[],[f27])).
% 1.96/0.65  fof(f27,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP3(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.96/0.65    inference(cnf_transformation,[],[f14])).
% 1.96/0.65  fof(f36,plain,(
% 1.96/0.65    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.96/0.65    inference(cnf_transformation,[],[f16])).
% 1.96/0.65  fof(f1406,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_xboole_0 = k2_relat_1(sK6(sK0,sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),sK1)),X1),X1)))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f867,f36,f35,f1395])).
% 1.96/0.65  fof(f1395,plain,(
% 1.96/0.65    ( ! [X9] : (sK1 != X9 | k1_xboole_0 = k2_relat_1(sK6(sK0,X9)) | ~v1_relat_1(sK6(sK0,X9)) | ~v1_funct_1(sK6(sK0,X9))) )),
% 1.96/0.65    inference(global_subsumption,[],[f45,f1389])).
% 1.96/0.65  fof(f1389,plain,(
% 1.96/0.65    ( ! [X9] : (sK1 != X9 | k1_xboole_0 = k2_relat_1(sK6(sK0,X9)) | k1_enumset1(sK1,sK1,sK1) = k2_relat_1(sK6(sK0,X9)) | ~v1_relat_1(sK6(sK0,X9)) | ~v1_funct_1(sK6(sK0,X9))) )),
% 1.96/0.65    inference(duplicate_literal_removal,[],[f1388])).
% 1.96/0.65  fof(f1388,plain,(
% 1.96/0.65    ( ! [X9] : (sK1 != X9 | k1_xboole_0 = k2_relat_1(sK6(sK0,X9)) | k1_enumset1(sK1,sK1,sK1) = k2_relat_1(sK6(sK0,X9)) | k1_xboole_0 = k2_relat_1(sK6(sK0,X9)) | ~v1_relat_1(sK6(sK0,X9)) | ~v1_funct_1(sK6(sK0,X9))) )),
% 1.96/0.65    inference(superposition,[],[f40,f1369])).
% 1.96/0.65  fof(f1369,plain,(
% 1.96/0.65    ( ! [X1] : (sK5(k2_relat_1(sK6(sK0,X1)),sK1) = X1 | k1_xboole_0 = k2_relat_1(sK6(sK0,X1)) | ~v1_relat_1(sK6(sK0,X1)) | ~v1_funct_1(sK6(sK0,X1))) )),
% 1.96/0.65    inference(resolution,[],[f816,f316])).
% 1.96/0.65  fof(f816,plain,(
% 1.96/0.65    ( ! [X2] : (sP3(sK5(k2_relat_1(sK6(sK0,X2)),sK1),sK6(sK0,X2)) | ~v1_funct_1(sK6(sK0,X2)) | k1_xboole_0 = k2_relat_1(sK6(sK0,X2)) | ~v1_relat_1(sK6(sK0,X2))) )),
% 1.96/0.65    inference(resolution,[],[f721,f42])).
% 1.96/0.65  fof(f721,plain,(
% 1.96/0.65    ( ! [X5] : (r2_hidden(sK5(k2_relat_1(sK6(sK0,X5)),sK1),k2_relat_1(sK6(sK0,X5))) | k1_xboole_0 = k2_relat_1(sK6(sK0,X5))) )),
% 1.96/0.65    inference(resolution,[],[f446,f185])).
% 1.96/0.65  fof(f185,plain,(
% 1.96/0.65    ( ! [X0] : (sP3(X0,sK6(sK0,X0))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f178,f73])).
% 1.96/0.65  fof(f178,plain,(
% 1.96/0.65    r2_hidden(sK2(k1_xboole_0,sK0),sK0)),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f18,f176])).
% 1.96/0.65  fof(f176,plain,(
% 1.96/0.65    ( ! [X1] : (r2_hidden(sK2(k1_xboole_0,X1),X1) | k1_xboole_0 = X1) )),
% 1.96/0.65    inference(global_subsumption,[],[f52,f53,f175])).
% 1.96/0.65  fof(f175,plain,(
% 1.96/0.65    ( ! [X1] : (k1_xboole_0 = X1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X1),X1)) )),
% 1.96/0.65    inference(forward_demodulation,[],[f170,f20])).
% 1.96/0.65  fof(f20,plain,(
% 1.96/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.96/0.65    inference(cnf_transformation,[],[f4])).
% 1.96/0.65  fof(f4,axiom,(
% 1.96/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.96/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.96/0.65  fof(f170,plain,(
% 1.96/0.65    ( ! [X1] : (~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X1),X1) | k2_relat_1(k1_xboole_0) = X1) )),
% 1.96/0.65    inference(resolution,[],[f29,f120])).
% 1.96/0.65  fof(f29,plain,(
% 1.96/0.65    ( ! [X0,X1] : (sP3(sK2(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.96/0.65    inference(cnf_transformation,[],[f14])).
% 1.96/0.65  fof(f53,plain,(
% 1.96/0.65    v1_relat_1(k1_xboole_0)),
% 1.96/0.65    inference(superposition,[],[f35,f46])).
% 1.96/0.65  fof(f52,plain,(
% 1.96/0.65    v1_funct_1(k1_xboole_0)),
% 1.96/0.65    inference(superposition,[],[f36,f46])).
% 1.96/0.65  fof(f18,plain,(
% 1.96/0.65    k1_xboole_0 != sK0),
% 1.96/0.65    inference(cnf_transformation,[],[f10])).
% 1.96/0.65  fof(f10,plain,(
% 1.96/0.65    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0)),
% 1.96/0.65    inference(ennf_transformation,[],[f9])).
% 1.96/0.65  fof(f9,negated_conjecture,(
% 1.96/0.65    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.96/0.65    inference(negated_conjecture,[],[f8])).
% 1.96/0.65  fof(f8,conjecture,(
% 1.96/0.65    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.96/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.96/0.65  fof(f446,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (~sP3(k2_relat_1(sK6(sK0,X1)),sK6(X2,X0)) | k1_xboole_0 = X0 | r2_hidden(sK5(X0,sK1),X0)) )),
% 1.96/0.65    inference(superposition,[],[f399,f41])).
% 1.96/0.65  fof(f41,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.96/0.65    inference(definition_unfolding,[],[f32,f38])).
% 1.96/0.65  fof(f38,plain,(
% 1.96/0.65    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.96/0.65    inference(definition_unfolding,[],[f21,f31])).
% 1.96/0.65  fof(f31,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f2])).
% 1.96/0.65  fof(f2,axiom,(
% 1.96/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.96/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.96/0.65  fof(f21,plain,(
% 1.96/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f1])).
% 1.96/0.65  fof(f1,axiom,(
% 1.96/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.96/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.96/0.65  fof(f32,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f15])).
% 1.96/0.65  fof(f15,plain,(
% 1.96/0.65    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.96/0.65    inference(ennf_transformation,[],[f3])).
% 1.96/0.65  fof(f3,axiom,(
% 1.96/0.65    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.96/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.96/0.65  fof(f399,plain,(
% 1.96/0.65    ( ! [X0,X1] : (~sP3(k2_relat_1(sK6(sK0,X0)),sK6(X1,k1_enumset1(sK1,sK1,sK1)))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f45,f316])).
% 1.96/0.65  fof(f40,plain,(
% 1.96/0.65    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 1.96/0.65    inference(definition_unfolding,[],[f33,f38])).
% 1.96/0.65  fof(f33,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 1.96/0.65    inference(cnf_transformation,[],[f15])).
% 1.96/0.65  fof(f45,plain,(
% 1.96/0.65    ( ! [X0] : (k1_enumset1(sK1,sK1,sK1) != k2_relat_1(sK6(sK0,X0))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f35,f36,f37,f39])).
% 1.96/0.65  fof(f39,plain,(
% 1.96/0.65    ( ! [X2] : (k2_relat_1(X2) != k1_enumset1(sK1,sK1,sK1) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | ~v1_relat_1(X2)) )),
% 1.96/0.65    inference(definition_unfolding,[],[f17,f38])).
% 1.96/0.65  fof(f17,plain,(
% 1.96/0.65    ( ! [X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | k2_relat_1(X2) != k1_tarski(sK1)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f10])).
% 1.96/0.65  fof(f197,plain,(
% 1.96/0.65    ( ! [X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(sK0,X1)),X0))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f188,f73])).
% 1.96/0.65  fof(f188,plain,(
% 1.96/0.65    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(sK0,X0)))) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f35,f36,f185,f43])).
% 1.96/0.65  fof(f120,plain,(
% 1.96/0.65    ( ! [X0] : (~sP3(X0,k1_xboole_0)) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f117,f56])).
% 1.96/0.65  fof(f56,plain,(
% 1.96/0.65    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) | ~sP3(X0,k1_xboole_0)) )),
% 1.96/0.65    inference(superposition,[],[f25,f19])).
% 1.96/0.65  fof(f19,plain,(
% 1.96/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.96/0.65    inference(cnf_transformation,[],[f4])).
% 1.96/0.65  fof(f117,plain,(
% 1.96/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f37,f111])).
% 1.96/0.65  fof(f111,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_enumset1(sK1,sK1,sK1) != X1 | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.96/0.65    inference(duplicate_literal_removal,[],[f109])).
% 1.96/0.65  fof(f109,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_enumset1(sK1,sK1,sK1) != X1 | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.96/0.65    inference(superposition,[],[f91,f68])).
% 1.96/0.65  fof(f68,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,X1) = X0 | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.96/0.65    inference(superposition,[],[f34,f46])).
% 1.96/0.65  fof(f91,plain,(
% 1.96/0.65    ( ! [X1] : (k1_enumset1(sK1,sK1,sK1) != k1_funct_1(k1_xboole_0,X1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.96/0.65    inference(superposition,[],[f45,f68])).
% 1.96/0.65  % SZS output end Proof for theBenchmark
% 1.96/0.65  % (26945)------------------------------
% 1.96/0.65  % (26945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.65  % (26945)Termination reason: Refutation
% 1.96/0.65  
% 1.96/0.65  % (26945)Memory used [KB]: 7419
% 1.96/0.65  % (26945)Time elapsed: 0.226 s
% 1.96/0.65  % (26945)------------------------------
% 1.96/0.65  % (26945)------------------------------
% 1.96/0.66  % (26919)Success in time 0.289 s
%------------------------------------------------------------------------------
