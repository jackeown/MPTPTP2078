%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:54 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   85 (1421 expanded)
%              Number of leaves         :    6 ( 344 expanded)
%              Depth                    :   31
%              Number of atoms          :  222 (5082 expanded)
%              Number of equality atoms :   95 (2173 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :   15 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1557,plain,(
    $false ),
    inference(global_subsumption,[],[f104,f1556])).

fof(f1556,plain,(
    ! [X0] : sP3(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1510,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f30,f32,f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f32,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f30,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f1510,plain,(
    ! [X0] : sP3(X0,sK6(k1_xboole_0,X0)) ),
    inference(superposition,[],[f186,f1488])).

fof(f1488,plain,(
    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1486,f1261])).

fof(f1261,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),X1)),X2)),X3)),X4)),X5),X5) = X4 ),
    inference(unit_resulting_resolution,[],[f859,f344])).

fof(f344,plain,(
    ! [X6,X8,X7,X5] :
      ( sK4(sK6(k2_relat_1(sK6(X5,X6)),X8),X7) = X6
      | ~ sP3(X7,sK6(k2_relat_1(sK6(X5,X6)),X8)) ) ),
    inference(global_subsumption,[],[f31,f30,f333])).

fof(f333,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ v1_funct_1(sK6(X5,X6))
      | ~ sP3(X7,sK6(k2_relat_1(sK6(X5,X6)),X8))
      | ~ v1_relat_1(sK6(X5,X6))
      | sK4(sK6(k2_relat_1(sK6(X5,X6)),X8),X7) = X6 ) ),
    inference(resolution,[],[f200,f238])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,sK6(X2,X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | ~ sP3(X1,sK6(X2,X0))
      | ~ sP3(X1,sK6(X2,X0)) ) ),
    inference(resolution,[],[f59,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ sP3(X2,sK6(X0,X1)) ) ),
    inference(superposition,[],[f21,f32])).

fof(f21,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f59,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(sK6(X3,X4),X5),X3)
      | X4 = X5
      | ~ sP3(X5,sK6(X3,X4)) ) ),
    inference(superposition,[],[f29,f22])).

fof(f22,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f200,plain,(
    ! [X10,X11,X9] :
      ( sP3(sK4(sK6(k2_relat_1(X10),X11),X9),X10)
      | ~ v1_funct_1(X10)
      | ~ sP3(X9,sK6(k2_relat_1(X10),X11))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f859,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X4)),X5)),X0)) ),
    inference(unit_resulting_resolution,[],[f794,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f60,f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f38,f29])).

fof(f38,plain,(
    ! [X0,X3] :
      ( sP3(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f794,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X4)),X0))) ),
    inference(unit_resulting_resolution,[],[f30,f31,f667,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP3(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f667,plain,(
    ! [X4,X2,X0,X3,X1] : sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X4)),X0)) ),
    inference(unit_resulting_resolution,[],[f645,f63])).

fof(f645,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X0))) ),
    inference(unit_resulting_resolution,[],[f30,f31,f278,f37])).

fof(f278,plain,(
    ! [X2,X0,X3,X1] : sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X0)) ),
    inference(unit_resulting_resolution,[],[f268,f63])).

fof(f268,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X0))) ),
    inference(unit_resulting_resolution,[],[f30,f31,f224,f37])).

fof(f224,plain,(
    ! [X2,X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X0)) ),
    inference(unit_resulting_resolution,[],[f209,f63])).

fof(f209,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X0))) ),
    inference(unit_resulting_resolution,[],[f30,f31,f186,f37])).

fof(f1486,plain,(
    ! [X4,X2,X0,X3,X1] : k1_xboole_0 = k2_relat_1(sK6(sK0,sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),X1)),X2)),X3)),sK1)),X4),X4))) ),
    inference(unit_resulting_resolution,[],[f1261,f39,f891])).

fof(f891,plain,(
    ! [X6,X8,X7] :
      ( X7 != X8
      | k1_xboole_0 = k2_relat_1(sK6(X6,X7))
      | k2_tarski(X8,X8) = k2_relat_1(sK6(X6,X7)) ) ),
    inference(duplicate_literal_removal,[],[f890])).

fof(f890,plain,(
    ! [X6,X8,X7] :
      ( X7 != X8
      | k1_xboole_0 = k2_relat_1(sK6(X6,X7))
      | k2_tarski(X8,X8) = k2_relat_1(sK6(X6,X7))
      | k2_tarski(X8,X8) = k2_relat_1(sK6(X6,X7))
      | k1_xboole_0 = k2_relat_1(sK6(X6,X7)) ) ),
    inference(superposition,[],[f34,f315])).

fof(f315,plain,(
    ! [X14,X12,X13] :
      ( sK5(k2_relat_1(sK6(X13,X12)),X14) = X12
      | k2_relat_1(sK6(X13,X12)) = k2_tarski(X14,X14)
      | k1_xboole_0 = k2_relat_1(sK6(X13,X12)) ) ),
    inference(global_subsumption,[],[f31,f30,f310])).

fof(f310,plain,(
    ! [X14,X12,X13] :
      ( sK5(k2_relat_1(sK6(X13,X12)),X14) = X12
      | k2_relat_1(sK6(X13,X12)) = k2_tarski(X14,X14)
      | ~ v1_funct_1(sK6(X13,X12))
      | k1_xboole_0 = k2_relat_1(sK6(X13,X12))
      | ~ v1_relat_1(sK6(X13,X12)) ) ),
    inference(resolution,[],[f238,f133])).

fof(f133,plain,(
    ! [X6,X7] :
      ( sP3(sK5(k2_relat_1(X6),X7),X6)
      | k2_relat_1(X6) = k2_tarski(X7,X7)
      | ~ v1_funct_1(X6)
      | k1_xboole_0 = k2_relat_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f27,f17])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f28,f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] : k2_tarski(sK1,sK1) != k2_relat_1(sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f30,f31,f32,f33])).

fof(f33,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k2_tarski(sK1,sK1)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f15,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | k2_relat_1(X2) != k1_tarski(sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f186,plain,(
    ! [X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(sK0,X1)),X0)) ),
    inference(unit_resulting_resolution,[],[f180,f63])).

fof(f180,plain,(
    ! [X0] : r2_hidden(X0,k2_relat_1(sK6(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f30,f31,f174,f37])).

fof(f174,plain,(
    ! [X0] : sP3(X0,sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f167,f63])).

fof(f167,plain,(
    r2_hidden(sK2(k1_xboole_0,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f16,f159])).

fof(f159,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f44,f45,f158])).

fof(f158,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0,X0),X0) ) ),
    inference(forward_demodulation,[],[f153,f151])).

fof(f151,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f45,f44,f99,f104,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP3(sK2(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f99,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f32,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_tarski(sK1,sK1) != X1
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_tarski(sK1,sK1) != X1
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f79,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k1_xboole_0,X1) = X0
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f29,f40])).

fof(f79,plain,(
    ! [X1] :
      ( k2_tarski(sK1,sK1) != k1_funct_1(k1_xboole_0,X1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f39,f58])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0,X0),X0)
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f25,f104])).

fof(f45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f30,f40])).

fof(f44,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f31,f40])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f104,plain,(
    ! [X0] : ~ sP3(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f56])).

fof(f56,plain,(
    ! [X3] :
      ( r2_hidden(sK4(k1_xboole_0,X3),k1_xboole_0)
      | ~ sP3(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f21,f43])).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f32,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:25:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (1220050944)
% 0.22/0.43  ipcrm: permission denied for id (1220706347)
% 0.22/0.43  ipcrm: permission denied for id (1220771887)
% 0.22/0.44  ipcrm: permission denied for id (1220804657)
% 0.22/0.44  ipcrm: permission denied for id (1220837427)
% 0.22/0.44  ipcrm: permission denied for id (1220870197)
% 0.22/0.45  ipcrm: permission denied for id (1220935737)
% 0.22/0.45  ipcrm: permission denied for id (1220968506)
% 0.22/0.45  ipcrm: permission denied for id (1221001276)
% 0.22/0.45  ipcrm: permission denied for id (1221034045)
% 0.22/0.45  ipcrm: permission denied for id (1221066816)
% 0.22/0.46  ipcrm: permission denied for id (1221099586)
% 0.22/0.46  ipcrm: permission denied for id (1221132356)
% 0.22/0.47  ipcrm: permission denied for id (1221165129)
% 0.22/0.47  ipcrm: permission denied for id (1221197900)
% 0.22/0.47  ipcrm: permission denied for id (1221230670)
% 0.22/0.47  ipcrm: permission denied for id (1221263439)
% 0.22/0.48  ipcrm: permission denied for id (1221394519)
% 0.22/0.49  ipcrm: permission denied for id (1221525598)
% 0.22/0.49  ipcrm: permission denied for id (1221558368)
% 0.22/0.50  ipcrm: permission denied for id (1221591140)
% 0.22/0.50  ipcrm: permission denied for id (1221623910)
% 0.22/0.51  ipcrm: permission denied for id (1221689450)
% 0.22/0.51  ipcrm: permission denied for id (1221722219)
% 0.22/0.51  ipcrm: permission denied for id (1221754989)
% 0.22/0.51  ipcrm: permission denied for id (1221787759)
% 0.22/0.53  ipcrm: permission denied for id (1222082685)
% 0.22/0.53  ipcrm: permission denied for id (1222115455)
% 0.41/0.65  % (6575)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.41/0.65  % (6591)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.41/0.67  % (6582)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.41/0.68  % (6582)Refutation not found, incomplete strategy% (6582)------------------------------
% 0.41/0.68  % (6582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.41/0.68  % (6582)Termination reason: Refutation not found, incomplete strategy
% 0.41/0.68  
% 0.41/0.68  % (6582)Memory used [KB]: 10618
% 0.41/0.68  % (6582)Time elapsed: 0.110 s
% 0.41/0.68  % (6582)------------------------------
% 0.41/0.68  % (6582)------------------------------
% 0.41/0.69  % (6600)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.41/0.69  % (6573)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.41/0.69  % (6573)Refutation not found, incomplete strategy% (6573)------------------------------
% 0.41/0.69  % (6573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.41/0.69  % (6573)Termination reason: Refutation not found, incomplete strategy
% 0.41/0.69  
% 0.41/0.69  % (6573)Memory used [KB]: 10618
% 0.41/0.69  % (6573)Time elapsed: 0.103 s
% 0.41/0.69  % (6573)------------------------------
% 0.41/0.69  % (6573)------------------------------
% 0.41/0.70  % (6581)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.41/0.70  % (6598)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.41/0.70  % (6572)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.41/0.70  % (6598)Refutation not found, incomplete strategy% (6598)------------------------------
% 0.41/0.70  % (6598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.41/0.70  % (6571)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.41/0.70  % (6598)Termination reason: Refutation not found, incomplete strategy
% 0.41/0.70  
% 0.41/0.70  % (6598)Memory used [KB]: 6268
% 0.41/0.70  % (6598)Time elapsed: 0.109 s
% 0.41/0.70  % (6598)------------------------------
% 0.41/0.70  % (6598)------------------------------
% 0.41/0.70  % (6590)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.41/0.70  % (6580)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.41/0.70  % (6590)Refutation not found, incomplete strategy% (6590)------------------------------
% 0.41/0.70  % (6590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.41/0.70  % (6590)Termination reason: Refutation not found, incomplete strategy
% 0.41/0.70  
% 0.41/0.70  % (6590)Memory used [KB]: 10618
% 0.41/0.70  % (6590)Time elapsed: 0.119 s
% 0.41/0.70  % (6590)------------------------------
% 0.41/0.70  % (6590)------------------------------
% 0.41/0.70  % (6579)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.41/0.70  % (6576)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.41/0.71  % (6599)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.41/0.71  % (6576)Refutation not found, incomplete strategy% (6576)------------------------------
% 0.41/0.71  % (6576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.41/0.71  % (6587)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.41/0.71  % (6577)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.41/0.71  % (6576)Termination reason: Refutation not found, incomplete strategy
% 0.41/0.71  
% 0.41/0.71  % (6576)Memory used [KB]: 6140
% 0.41/0.71  % (6576)Time elapsed: 0.124 s
% 0.41/0.71  % (6576)------------------------------
% 0.41/0.71  % (6576)------------------------------
% 0.41/0.71  % (6588)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.41/0.71  % (6597)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.41/0.71  % (6601)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.41/0.71  % (6580)Refutation not found, incomplete strategy% (6580)------------------------------
% 0.41/0.71  % (6580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.41/0.71  % (6580)Termination reason: Refutation not found, incomplete strategy
% 0.41/0.71  
% 0.41/0.71  % (6580)Memory used [KB]: 10618
% 0.41/0.71  % (6580)Time elapsed: 0.130 s
% 0.41/0.71  % (6580)------------------------------
% 0.41/0.71  % (6580)------------------------------
% 0.63/0.71  % (6586)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.63/0.72  % (6592)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.63/0.72  % (6596)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.63/0.72  % (6583)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.63/0.72  % (6583)Refutation not found, incomplete strategy% (6583)------------------------------
% 0.63/0.72  % (6583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.63/0.72  % (6593)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.63/0.72  % (6594)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.63/0.72  % (6583)Termination reason: Refutation not found, incomplete strategy
% 0.63/0.72  
% 0.63/0.72  % (6583)Memory used [KB]: 10618
% 0.63/0.72  % (6583)Time elapsed: 0.140 s
% 0.63/0.72  % (6583)------------------------------
% 0.63/0.72  % (6583)------------------------------
% 0.63/0.72  % (6594)Refutation not found, incomplete strategy% (6594)------------------------------
% 0.63/0.72  % (6594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.63/0.72  % (6594)Termination reason: Refutation not found, incomplete strategy
% 0.63/0.72  
% 0.63/0.72  % (6594)Memory used [KB]: 1663
% 0.63/0.72  % (6594)Time elapsed: 0.137 s
% 0.63/0.72  % (6594)------------------------------
% 0.63/0.72  % (6594)------------------------------
% 0.63/0.72  % (6602)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.63/0.73  % (6584)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.63/0.73  % (6599)Refutation not found, incomplete strategy% (6599)------------------------------
% 0.63/0.73  % (6599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.63/0.73  % (6578)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.63/0.73  % (6595)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.63/0.73  % (6599)Termination reason: Refutation not found, incomplete strategy
% 0.63/0.73  
% 0.63/0.73  % (6599)Memory used [KB]: 10746
% 0.63/0.73  % (6599)Time elapsed: 0.144 s
% 0.63/0.73  % (6599)------------------------------
% 0.63/0.73  % (6599)------------------------------
% 0.63/0.73  % (6585)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.63/0.73  % (6595)Refutation not found, incomplete strategy% (6595)------------------------------
% 0.63/0.73  % (6595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.63/0.73  % (6595)Termination reason: Refutation not found, incomplete strategy
% 0.63/0.73  
% 0.63/0.73  % (6595)Memory used [KB]: 10618
% 0.63/0.73  % (6595)Time elapsed: 0.147 s
% 0.63/0.73  % (6595)------------------------------
% 0.63/0.73  % (6595)------------------------------
% 0.63/0.74  % (6593)Refutation not found, incomplete strategy% (6593)------------------------------
% 0.63/0.74  % (6593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.63/0.74  % (6593)Termination reason: Refutation not found, incomplete strategy
% 0.63/0.74  
% 0.63/0.74  % (6593)Memory used [KB]: 10618
% 0.63/0.74  % (6593)Time elapsed: 0.157 s
% 0.63/0.74  % (6593)------------------------------
% 0.63/0.74  % (6593)------------------------------
% 0.91/0.80  % (6680)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.91/0.80  % (6597)Refutation found. Thanks to Tanya!
% 0.91/0.80  % SZS status Theorem for theBenchmark
% 0.91/0.81  % SZS output start Proof for theBenchmark
% 0.91/0.81  fof(f1557,plain,(
% 0.91/0.81    $false),
% 0.91/0.81    inference(global_subsumption,[],[f104,f1556])).
% 0.91/0.81  fof(f1556,plain,(
% 0.91/0.81    ( ! [X0] : (sP3(X0,k1_xboole_0)) )),
% 0.91/0.81    inference(forward_demodulation,[],[f1510,f40])).
% 0.91/0.81  fof(f40,plain,(
% 0.91/0.81    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f30,f32,f18])).
% 0.91/0.81  fof(f18,plain,(
% 0.91/0.81    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.91/0.81    inference(cnf_transformation,[],[f10])).
% 0.91/0.81  fof(f10,plain,(
% 0.91/0.81    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.91/0.81    inference(flattening,[],[f9])).
% 0.91/0.81  fof(f9,plain,(
% 0.91/0.81    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.91/0.81    inference(ennf_transformation,[],[f3])).
% 0.91/0.81  fof(f3,axiom,(
% 0.91/0.81    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.91/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.91/0.81  fof(f32,plain,(
% 0.91/0.81    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 0.91/0.81    inference(cnf_transformation,[],[f14])).
% 0.91/0.81  fof(f14,plain,(
% 0.91/0.81    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.91/0.81    inference(ennf_transformation,[],[f5])).
% 0.91/0.81  fof(f5,axiom,(
% 0.91/0.81    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.91/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.91/0.81  fof(f30,plain,(
% 0.91/0.81    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 0.91/0.81    inference(cnf_transformation,[],[f14])).
% 0.91/0.81  fof(f1510,plain,(
% 0.91/0.81    ( ! [X0] : (sP3(X0,sK6(k1_xboole_0,X0))) )),
% 0.91/0.81    inference(superposition,[],[f186,f1488])).
% 0.91/0.81  fof(f1488,plain,(
% 0.91/0.81    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1))),
% 0.91/0.81    inference(forward_demodulation,[],[f1486,f1261])).
% 0.91/0.81  fof(f1261,plain,(
% 0.91/0.81    ( ! [X4,X2,X0,X5,X3,X1] : (sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),X1)),X2)),X3)),X4)),X5),X5) = X4) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f859,f344])).
% 0.91/0.81  fof(f344,plain,(
% 0.91/0.81    ( ! [X6,X8,X7,X5] : (sK4(sK6(k2_relat_1(sK6(X5,X6)),X8),X7) = X6 | ~sP3(X7,sK6(k2_relat_1(sK6(X5,X6)),X8))) )),
% 0.91/0.81    inference(global_subsumption,[],[f31,f30,f333])).
% 0.91/0.81  fof(f333,plain,(
% 0.91/0.81    ( ! [X6,X8,X7,X5] : (~v1_funct_1(sK6(X5,X6)) | ~sP3(X7,sK6(k2_relat_1(sK6(X5,X6)),X8)) | ~v1_relat_1(sK6(X5,X6)) | sK4(sK6(k2_relat_1(sK6(X5,X6)),X8),X7) = X6) )),
% 0.91/0.81    inference(resolution,[],[f200,f238])).
% 0.91/0.81  fof(f238,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (~sP3(X1,sK6(X2,X0)) | X0 = X1) )),
% 0.91/0.81    inference(duplicate_literal_removal,[],[f232])).
% 0.91/0.81  fof(f232,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (X0 = X1 | ~sP3(X1,sK6(X2,X0)) | ~sP3(X1,sK6(X2,X0))) )),
% 0.91/0.81    inference(resolution,[],[f59,f55])).
% 0.91/0.81  fof(f55,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~sP3(X2,sK6(X0,X1))) )),
% 0.91/0.81    inference(superposition,[],[f21,f32])).
% 0.91/0.81  fof(f21,plain,(
% 0.91/0.81    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 0.91/0.81    inference(cnf_transformation,[],[f12])).
% 0.91/0.81  fof(f12,plain,(
% 0.91/0.81    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.91/0.81    inference(flattening,[],[f11])).
% 0.91/0.81  fof(f11,plain,(
% 0.91/0.81    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.91/0.81    inference(ennf_transformation,[],[f4])).
% 0.91/0.81  fof(f4,axiom,(
% 0.91/0.81    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.91/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.91/0.81  fof(f59,plain,(
% 0.91/0.81    ( ! [X4,X5,X3] : (~r2_hidden(sK4(sK6(X3,X4),X5),X3) | X4 = X5 | ~sP3(X5,sK6(X3,X4))) )),
% 0.91/0.81    inference(superposition,[],[f29,f22])).
% 0.91/0.81  fof(f22,plain,(
% 0.91/0.81    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 0.91/0.81    inference(cnf_transformation,[],[f12])).
% 0.91/0.81  fof(f29,plain,(
% 0.91/0.81    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.91/0.81    inference(cnf_transformation,[],[f14])).
% 0.91/0.81  fof(f200,plain,(
% 0.91/0.81    ( ! [X10,X11,X9] : (sP3(sK4(sK6(k2_relat_1(X10),X11),X9),X10) | ~v1_funct_1(X10) | ~sP3(X9,sK6(k2_relat_1(X10),X11)) | ~v1_relat_1(X10)) )),
% 0.91/0.81    inference(resolution,[],[f55,f36])).
% 0.91/0.81  fof(f36,plain,(
% 0.91/0.81    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 0.91/0.81    inference(equality_resolution,[],[f24])).
% 0.91/0.81  fof(f24,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.91/0.81    inference(cnf_transformation,[],[f12])).
% 0.91/0.81  fof(f31,plain,(
% 0.91/0.81    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 0.91/0.81    inference(cnf_transformation,[],[f14])).
% 0.91/0.81  fof(f859,plain,(
% 0.91/0.81    ( ! [X4,X2,X0,X5,X3,X1] : (sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X4)),X5)),X0))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f794,f63])).
% 0.91/0.81  fof(f63,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 0.91/0.81    inference(duplicate_literal_removal,[],[f62])).
% 0.91/0.81  fof(f62,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 0.91/0.81    inference(forward_demodulation,[],[f60,f32])).
% 0.91/0.81  fof(f60,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 0.91/0.81    inference(superposition,[],[f38,f29])).
% 0.91/0.81  fof(f38,plain,(
% 0.91/0.81    ( ! [X0,X3] : (sP3(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.91/0.81    inference(equality_resolution,[],[f20])).
% 0.91/0.81  fof(f20,plain,(
% 0.91/0.81    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP3(X2,X0)) )),
% 0.91/0.81    inference(cnf_transformation,[],[f12])).
% 0.91/0.81  fof(f794,plain,(
% 0.91/0.81    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X4)),X0)))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f30,f31,f667,f37])).
% 0.91/0.81  fof(f37,plain,(
% 0.91/0.81    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 0.91/0.81    inference(equality_resolution,[],[f23])).
% 0.91/0.81  fof(f23,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP3(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.91/0.81    inference(cnf_transformation,[],[f12])).
% 0.91/0.81  fof(f667,plain,(
% 0.91/0.81    ( ! [X4,X2,X0,X3,X1] : (sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X4)),X0))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f645,f63])).
% 0.91/0.81  fof(f645,plain,(
% 0.91/0.81    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X0)))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f30,f31,f278,f37])).
% 0.91/0.81  fof(f278,plain,(
% 0.91/0.81    ( ! [X2,X0,X3,X1] : (sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X3)),X0))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f268,f63])).
% 0.91/0.81  fof(f268,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X0)))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f30,f31,f224,f37])).
% 0.91/0.81  fof(f224,plain,(
% 0.91/0.81    ( ! [X2,X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X2)),X0))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f209,f63])).
% 0.91/0.81  fof(f209,plain,(
% 0.91/0.81    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK6(sK0,X1)),X0)))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f30,f31,f186,f37])).
% 0.91/0.81  fof(f1486,plain,(
% 0.91/0.81    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = k2_relat_1(sK6(sK0,sK4(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(sK0,X0)),X1)),X2)),X3)),sK1)),X4),X4)))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f1261,f39,f891])).
% 0.91/0.81  fof(f891,plain,(
% 0.91/0.81    ( ! [X6,X8,X7] : (X7 != X8 | k1_xboole_0 = k2_relat_1(sK6(X6,X7)) | k2_tarski(X8,X8) = k2_relat_1(sK6(X6,X7))) )),
% 0.91/0.81    inference(duplicate_literal_removal,[],[f890])).
% 0.91/0.81  fof(f890,plain,(
% 0.91/0.81    ( ! [X6,X8,X7] : (X7 != X8 | k1_xboole_0 = k2_relat_1(sK6(X6,X7)) | k2_tarski(X8,X8) = k2_relat_1(sK6(X6,X7)) | k2_tarski(X8,X8) = k2_relat_1(sK6(X6,X7)) | k1_xboole_0 = k2_relat_1(sK6(X6,X7))) )),
% 0.91/0.81    inference(superposition,[],[f34,f315])).
% 0.91/0.81  fof(f315,plain,(
% 0.91/0.81    ( ! [X14,X12,X13] : (sK5(k2_relat_1(sK6(X13,X12)),X14) = X12 | k2_relat_1(sK6(X13,X12)) = k2_tarski(X14,X14) | k1_xboole_0 = k2_relat_1(sK6(X13,X12))) )),
% 0.91/0.81    inference(global_subsumption,[],[f31,f30,f310])).
% 0.91/0.81  fof(f310,plain,(
% 0.91/0.81    ( ! [X14,X12,X13] : (sK5(k2_relat_1(sK6(X13,X12)),X14) = X12 | k2_relat_1(sK6(X13,X12)) = k2_tarski(X14,X14) | ~v1_funct_1(sK6(X13,X12)) | k1_xboole_0 = k2_relat_1(sK6(X13,X12)) | ~v1_relat_1(sK6(X13,X12))) )),
% 0.91/0.81    inference(resolution,[],[f238,f133])).
% 0.91/0.81  fof(f133,plain,(
% 0.91/0.81    ( ! [X6,X7] : (sP3(sK5(k2_relat_1(X6),X7),X6) | k2_relat_1(X6) = k2_tarski(X7,X7) | ~v1_funct_1(X6) | k1_xboole_0 = k2_relat_1(X6) | ~v1_relat_1(X6)) )),
% 0.91/0.81    inference(resolution,[],[f35,f36])).
% 0.91/0.81  fof(f35,plain,(
% 0.91/0.81    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 0.91/0.81    inference(definition_unfolding,[],[f27,f17])).
% 0.91/0.81  fof(f17,plain,(
% 0.91/0.81    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.91/0.81    inference(cnf_transformation,[],[f1])).
% 0.91/0.81  fof(f1,axiom,(
% 0.91/0.81    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.91/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.91/0.81  fof(f27,plain,(
% 0.91/0.81    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.91/0.81    inference(cnf_transformation,[],[f13])).
% 0.91/0.81  fof(f13,plain,(
% 0.91/0.81    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.91/0.81    inference(ennf_transformation,[],[f2])).
% 0.91/0.81  fof(f2,axiom,(
% 0.91/0.81    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.91/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.91/0.81  fof(f34,plain,(
% 0.91/0.81    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 0.91/0.81    inference(definition_unfolding,[],[f28,f17])).
% 0.91/0.81  fof(f28,plain,(
% 0.91/0.81    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 0.91/0.81    inference(cnf_transformation,[],[f13])).
% 0.91/0.81  fof(f39,plain,(
% 0.91/0.81    ( ! [X0] : (k2_tarski(sK1,sK1) != k2_relat_1(sK6(sK0,X0))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f30,f31,f32,f33])).
% 0.91/0.81  fof(f33,plain,(
% 0.91/0.81    ( ! [X2] : (k2_relat_1(X2) != k2_tarski(sK1,sK1) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | ~v1_relat_1(X2)) )),
% 0.91/0.81    inference(definition_unfolding,[],[f15,f17])).
% 0.91/0.81  fof(f15,plain,(
% 0.91/0.81    ( ! [X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | k2_relat_1(X2) != k1_tarski(sK1)) )),
% 0.91/0.81    inference(cnf_transformation,[],[f8])).
% 0.91/0.81  fof(f8,plain,(
% 0.91/0.81    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0)),
% 0.91/0.81    inference(ennf_transformation,[],[f7])).
% 0.91/0.81  fof(f7,negated_conjecture,(
% 0.91/0.81    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.91/0.81    inference(negated_conjecture,[],[f6])).
% 0.91/0.81  fof(f6,conjecture,(
% 0.91/0.81    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.91/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.91/0.81  fof(f186,plain,(
% 0.91/0.81    ( ! [X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(sK0,X1)),X0))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f180,f63])).
% 0.91/0.81  fof(f180,plain,(
% 0.91/0.81    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(sK0,X0)))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f30,f31,f174,f37])).
% 0.91/0.81  fof(f174,plain,(
% 0.91/0.81    ( ! [X0] : (sP3(X0,sK6(sK0,X0))) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f167,f63])).
% 0.91/0.81  fof(f167,plain,(
% 0.91/0.81    r2_hidden(sK2(k1_xboole_0,sK0),sK0)),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f16,f159])).
% 0.91/0.81  fof(f159,plain,(
% 0.91/0.81    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 0.91/0.81    inference(global_subsumption,[],[f44,f45,f158])).
% 0.91/0.81  fof(f158,plain,(
% 0.91/0.81    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X0),X0)) )),
% 0.91/0.81    inference(forward_demodulation,[],[f153,f151])).
% 0.91/0.81  fof(f151,plain,(
% 0.91/0.81    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f45,f44,f99,f104,f25])).
% 0.91/0.81  fof(f25,plain,(
% 0.91/0.81    ( ! [X0,X1] : (sP3(sK2(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.91/0.81    inference(cnf_transformation,[],[f12])).
% 0.91/0.81  fof(f99,plain,(
% 0.91/0.81    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f32,f98])).
% 0.91/0.81  fof(f98,plain,(
% 0.91/0.81    ( ! [X0,X1] : (k2_tarski(sK1,sK1) != X1 | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.91/0.81    inference(duplicate_literal_removal,[],[f96])).
% 0.91/0.81  fof(f96,plain,(
% 0.91/0.81    ( ! [X0,X1] : (k2_tarski(sK1,sK1) != X1 | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.91/0.81    inference(superposition,[],[f79,f58])).
% 0.91/0.81  fof(f58,plain,(
% 0.91/0.81    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,X1) = X0 | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.91/0.81    inference(superposition,[],[f29,f40])).
% 0.91/0.81  fof(f79,plain,(
% 0.91/0.81    ( ! [X1] : (k2_tarski(sK1,sK1) != k1_funct_1(k1_xboole_0,X1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.91/0.81    inference(superposition,[],[f39,f58])).
% 0.91/0.81  fof(f153,plain,(
% 0.91/0.81    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X0),X0) | k2_relat_1(k1_xboole_0) = X0) )),
% 0.91/0.81    inference(resolution,[],[f25,f104])).
% 0.91/0.81  fof(f45,plain,(
% 0.91/0.81    v1_relat_1(k1_xboole_0)),
% 0.91/0.81    inference(superposition,[],[f30,f40])).
% 0.91/0.81  fof(f44,plain,(
% 0.91/0.81    v1_funct_1(k1_xboole_0)),
% 0.91/0.81    inference(superposition,[],[f31,f40])).
% 0.91/0.81  fof(f16,plain,(
% 0.91/0.81    k1_xboole_0 != sK0),
% 0.91/0.81    inference(cnf_transformation,[],[f8])).
% 0.91/0.81  fof(f104,plain,(
% 0.91/0.81    ( ! [X0] : (~sP3(X0,k1_xboole_0)) )),
% 0.91/0.81    inference(unit_resulting_resolution,[],[f99,f56])).
% 0.91/0.81  fof(f56,plain,(
% 0.91/0.81    ( ! [X3] : (r2_hidden(sK4(k1_xboole_0,X3),k1_xboole_0) | ~sP3(X3,k1_xboole_0)) )),
% 0.91/0.81    inference(superposition,[],[f21,f43])).
% 0.91/0.81  fof(f43,plain,(
% 0.91/0.81    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.91/0.81    inference(superposition,[],[f32,f40])).
% 0.91/0.81  % SZS output end Proof for theBenchmark
% 0.91/0.81  % (6597)------------------------------
% 0.91/0.81  % (6597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.91/0.81  % (6597)Termination reason: Refutation
% 0.91/0.81  
% 0.91/0.81  % (6597)Memory used [KB]: 7291
% 0.91/0.81  % (6597)Time elapsed: 0.223 s
% 0.91/0.81  % (6597)------------------------------
% 0.91/0.81  % (6597)------------------------------
% 0.91/0.81  % (6386)Success in time 0.433 s
%------------------------------------------------------------------------------
