%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:13 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 237 expanded)
%              Number of leaves         :    7 (  69 expanded)
%              Depth                    :   22
%              Number of atoms          :  251 (1129 expanded)
%              Number of equality atoms :  250 (1128 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1661,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f24,f24,f25,f1397,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f1397,plain,(
    ! [X71] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71) ),
    inference(subsumption_resolution,[],[f1396,f24])).

fof(f1396,plain,(
    ! [X71] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71) ) ),
    inference(subsumption_resolution,[],[f1395,f25])).

fof(f1395,plain,(
    ! [X71] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71) ) ),
    inference(subsumption_resolution,[],[f1394,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f1394,plain,(
    ! [X71] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71) ) ),
    inference(subsumption_resolution,[],[f1383,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f1383,plain,(
    ! [X71] :
      ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71) ) ),
    inference(trivial_inequality_removal,[],[f1332])).

fof(f1332,plain,(
    ! [X71] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71) ) ),
    inference(superposition,[],[f62,f1300])).

fof(f1300,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f1282,f1160])).

fof(f1160,plain,(
    ! [X0] :
      ( sK0 != sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(trivial_inequality_removal,[],[f1159])).

fof(f1159,plain,(
    ! [X0] :
      ( sK1 != sK1
      | sK0 != sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f1144])).

fof(f1144,plain,(
    ! [X0] :
      ( sK1 != sK1
      | sK0 != sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ) ),
    inference(superposition,[],[f330,f1122])).

fof(f1122,plain,(
    ! [X0] :
      ( sK1 = sK5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ) ),
    inference(equality_resolution,[],[f587])).

fof(f587,plain,(
    ! [X17,X15,X18,X16] :
      ( k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X15)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X15)
      | sK5 = X17
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ) ),
    inference(superposition,[],[f64,f574])).

fof(f574,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(equality_resolution,[],[f291])).

fof(f291,plain,(
    ! [X6,X7,X5] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)
      | k2_zfmisc_1(sK4,sK5) = X5 ) ),
    inference(superposition,[],[f65,f50])).

fof(f50,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f23,f49,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f40,f30])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f23,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f46,f30,f30,f30])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f47,f30,f30,f30])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f330,plain,
    ( sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(subsumption_resolution,[],[f329,f324])).

fof(f324,plain,
    ( sK2 = sK6
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(equality_resolution,[],[f259])).

fof(f259,plain,(
    ! [X6,X7,X5] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)
      | sK6 = X6 ) ),
    inference(superposition,[],[f64,f50])).

fof(f329,plain,
    ( sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(trivial_inequality_removal,[],[f328])).

fof(f328,plain,
    ( sK3 != sK3
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(superposition,[],[f28,f312])).

fof(f312,plain,
    ( sK3 = sK7
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(equality_resolution,[],[f231])).

fof(f231,plain,(
    ! [X6,X7,X5] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)
      | sK7 = X7 ) ),
    inference(superposition,[],[f63,f50])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f48,f30,f30,f30])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f18])).

fof(f1282,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
      | sK0 = sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ) ),
    inference(equality_resolution,[],[f589])).

fof(f589,plain,(
    ! [X26,X24,X23,X25] :
      ( k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X23)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X23)
      | sK4 = X24
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ) ),
    inference(superposition,[],[f65,f574])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (6058)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (6073)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (6065)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (6065)Refutation not found, incomplete strategy% (6065)------------------------------
% 0.20/0.53  % (6065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6065)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6065)Memory used [KB]: 1663
% 0.20/0.53  % (6065)Time elapsed: 0.028 s
% 0.20/0.53  % (6065)------------------------------
% 0.20/0.53  % (6065)------------------------------
% 0.20/0.54  % (6059)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (6066)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.56  % (6054)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.58  % (6076)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.58  % (6070)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.58  % (6075)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.58  % (6074)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.58  % (6062)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.59  % (6067)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.59  % (6078)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.59  % (6067)Refutation not found, incomplete strategy% (6067)------------------------------
% 0.20/0.59  % (6067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (6067)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (6067)Memory used [KB]: 10618
% 0.20/0.59  % (6067)Time elapsed: 0.171 s
% 0.20/0.59  % (6067)------------------------------
% 0.20/0.59  % (6067)------------------------------
% 0.20/0.59  % (6052)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.60  % (6060)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.60  % (6053)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.60  % (6056)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.61  % (6057)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.62  % (6077)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.62  % (6079)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.62  % (6051)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.62  % (6080)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.62  % (6068)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.62  % (6080)Refutation not found, incomplete strategy% (6080)------------------------------
% 0.20/0.62  % (6080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.62  % (6080)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.62  
% 0.20/0.62  % (6080)Memory used [KB]: 1791
% 0.20/0.62  % (6080)Time elapsed: 0.197 s
% 0.20/0.62  % (6080)------------------------------
% 0.20/0.62  % (6080)------------------------------
% 0.20/0.63  % (6071)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.63  % (6055)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.63  % (6069)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.91/0.63  % (6063)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.91/0.63  % (6069)Refutation not found, incomplete strategy% (6069)------------------------------
% 1.91/0.63  % (6069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.63  % (6069)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.63  
% 1.91/0.63  % (6069)Memory used [KB]: 1663
% 1.91/0.63  % (6069)Time elapsed: 0.196 s
% 1.91/0.63  % (6069)------------------------------
% 1.91/0.63  % (6069)------------------------------
% 1.91/0.63  % (6063)Refutation not found, incomplete strategy% (6063)------------------------------
% 1.91/0.63  % (6063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.63  % (6063)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.63  
% 1.91/0.63  % (6063)Memory used [KB]: 10746
% 1.91/0.63  % (6063)Time elapsed: 0.208 s
% 1.91/0.63  % (6063)------------------------------
% 1.91/0.63  % (6063)------------------------------
% 1.91/0.63  % (6061)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.91/0.64  % (6072)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.91/0.64  % (6064)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.91/0.64  % (6077)Refutation not found, incomplete strategy% (6077)------------------------------
% 1.91/0.64  % (6077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.64  % (6077)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.64  
% 1.91/0.64  % (6077)Memory used [KB]: 6268
% 1.91/0.64  % (6077)Time elapsed: 0.206 s
% 1.91/0.64  % (6077)------------------------------
% 1.91/0.64  % (6077)------------------------------
% 2.29/0.66  % (6073)Refutation found. Thanks to Tanya!
% 2.29/0.66  % SZS status Theorem for theBenchmark
% 2.29/0.66  % SZS output start Proof for theBenchmark
% 2.29/0.66  fof(f1661,plain,(
% 2.29/0.66    $false),
% 2.29/0.66    inference(unit_resulting_resolution,[],[f24,f24,f25,f1397,f57])).
% 2.29/0.66  fof(f57,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.29/0.66    inference(definition_unfolding,[],[f36,f30])).
% 2.29/0.66  fof(f30,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f3])).
% 2.29/0.66  fof(f3,axiom,(
% 2.29/0.66    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.29/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.29/0.66  fof(f36,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.29/0.66    inference(cnf_transformation,[],[f20])).
% 2.29/0.66  fof(f20,plain,(
% 2.29/0.66    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.29/0.66    inference(flattening,[],[f19])).
% 2.29/0.66  fof(f19,plain,(
% 2.29/0.66    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.29/0.66    inference(nnf_transformation,[],[f5])).
% 2.29/0.66  fof(f5,axiom,(
% 2.29/0.66    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 2.29/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 2.29/0.66  fof(f1397,plain,(
% 2.29/0.66    ( ! [X71] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f1396,f24])).
% 2.29/0.66  fof(f1396,plain,(
% 2.29/0.66    ( ! [X71] : (k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f1395,f25])).
% 2.29/0.66  fof(f1395,plain,(
% 2.29/0.66    ( ! [X71] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f1394,f26])).
% 2.29/0.66  fof(f26,plain,(
% 2.29/0.66    k1_xboole_0 != sK2),
% 2.29/0.66    inference(cnf_transformation,[],[f18])).
% 2.29/0.66  fof(f18,plain,(
% 2.29/0.66    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 2.29/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f17])).
% 2.29/0.66  fof(f17,plain,(
% 2.29/0.66    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.29/0.66    introduced(choice_axiom,[])).
% 2.29/0.66  fof(f12,plain,(
% 2.29/0.66    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 2.29/0.66    inference(flattening,[],[f11])).
% 2.29/0.66  fof(f11,plain,(
% 2.29/0.66    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 2.29/0.66    inference(ennf_transformation,[],[f10])).
% 2.29/0.66  fof(f10,negated_conjecture,(
% 2.29/0.66    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.29/0.66    inference(negated_conjecture,[],[f9])).
% 2.29/0.66  fof(f9,conjecture,(
% 2.29/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.29/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).
% 2.29/0.66  fof(f1394,plain,(
% 2.29/0.66    ( ! [X71] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f1383,f27])).
% 2.29/0.66  fof(f27,plain,(
% 2.29/0.66    k1_xboole_0 != sK3),
% 2.29/0.66    inference(cnf_transformation,[],[f18])).
% 2.29/0.66  fof(f1383,plain,(
% 2.29/0.66    ( ! [X71] : (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71)) )),
% 2.29/0.66    inference(trivial_inequality_removal,[],[f1332])).
% 2.29/0.66  fof(f1332,plain,(
% 2.29/0.66    ( ! [X71] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X71)) )),
% 2.29/0.66    inference(superposition,[],[f62,f1300])).
% 2.29/0.66  fof(f1300,plain,(
% 2.29/0.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f1282,f1160])).
% 2.29/0.66  fof(f1160,plain,(
% 2.29/0.66    ( ! [X0] : (sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 2.29/0.66    inference(trivial_inequality_removal,[],[f1159])).
% 2.29/0.66  fof(f1159,plain,(
% 2.29/0.66    ( ! [X0] : (sK1 != sK1 | sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 2.29/0.66    inference(duplicate_literal_removal,[],[f1144])).
% 2.29/0.66  fof(f1144,plain,(
% 2.29/0.66    ( ! [X0] : (sK1 != sK1 | sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) )),
% 2.29/0.66    inference(superposition,[],[f330,f1122])).
% 2.29/0.66  fof(f1122,plain,(
% 2.29/0.66    ( ! [X0] : (sK1 = sK5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) )),
% 2.29/0.66    inference(equality_resolution,[],[f587])).
% 2.29/0.66  fof(f587,plain,(
% 2.29/0.66    ( ! [X17,X15,X18,X16] : (k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X15) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X15) | sK5 = X17 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) )),
% 2.29/0.66    inference(superposition,[],[f64,f574])).
% 2.29/0.66  fof(f574,plain,(
% 2.29/0.66    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 2.29/0.66    inference(equality_resolution,[],[f291])).
% 2.29/0.66  fof(f291,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7) | k2_zfmisc_1(sK4,sK5) = X5) )),
% 2.29/0.66    inference(superposition,[],[f65,f50])).
% 2.29/0.66  fof(f50,plain,(
% 2.29/0.66    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 2.29/0.66    inference(definition_unfolding,[],[f23,f49,f49])).
% 2.29/0.66  fof(f49,plain,(
% 2.29/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.29/0.66    inference(definition_unfolding,[],[f40,f30])).
% 2.29/0.66  fof(f40,plain,(
% 2.29/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f4])).
% 2.29/0.66  fof(f4,axiom,(
% 2.29/0.66    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.29/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.29/0.66  fof(f23,plain,(
% 2.29/0.66    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 2.29/0.66    inference(cnf_transformation,[],[f18])).
% 2.29/0.66  fof(f65,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X0 = X3) )),
% 2.29/0.66    inference(definition_unfolding,[],[f46,f30,f30,f30])).
% 2.29/0.66  fof(f46,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f16])).
% 2.29/0.66  fof(f16,plain,(
% 2.29/0.66    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 2.29/0.66    inference(flattening,[],[f15])).
% 2.29/0.66  fof(f15,plain,(
% 2.29/0.66    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 2.29/0.66    inference(ennf_transformation,[],[f6])).
% 2.29/0.66  fof(f6,axiom,(
% 2.29/0.66    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 2.29/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).
% 2.29/0.66  fof(f64,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X1 = X4) )),
% 2.29/0.66    inference(definition_unfolding,[],[f47,f30,f30,f30])).
% 2.29/0.66  fof(f47,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f16])).
% 2.29/0.66  fof(f330,plain,(
% 2.29/0.66    sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 2.29/0.66    inference(subsumption_resolution,[],[f329,f324])).
% 2.29/0.66  fof(f324,plain,(
% 2.29/0.66    sK2 = sK6 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 2.29/0.66    inference(equality_resolution,[],[f259])).
% 2.29/0.66  fof(f259,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7) | sK6 = X6) )),
% 2.29/0.66    inference(superposition,[],[f64,f50])).
% 2.29/0.66  fof(f329,plain,(
% 2.29/0.66    sK2 != sK6 | sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 2.29/0.66    inference(trivial_inequality_removal,[],[f328])).
% 2.29/0.66  fof(f328,plain,(
% 2.29/0.66    sK3 != sK3 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 2.29/0.66    inference(superposition,[],[f28,f312])).
% 2.29/0.66  fof(f312,plain,(
% 2.29/0.66    sK3 = sK7 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 2.29/0.66    inference(equality_resolution,[],[f231])).
% 2.29/0.66  fof(f231,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7) | sK7 = X7) )),
% 2.29/0.66    inference(superposition,[],[f63,f50])).
% 2.29/0.66  fof(f63,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X2 = X5) )),
% 2.29/0.66    inference(definition_unfolding,[],[f48,f30,f30,f30])).
% 2.29/0.66  fof(f48,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f16])).
% 2.29/0.66  fof(f28,plain,(
% 2.29/0.66    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 2.29/0.66    inference(cnf_transformation,[],[f18])).
% 2.29/0.66  fof(f1282,plain,(
% 2.29/0.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) | sK0 = sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) )),
% 2.29/0.66    inference(equality_resolution,[],[f589])).
% 2.29/0.66  fof(f589,plain,(
% 2.29/0.66    ( ! [X26,X24,X23,X25] : (k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X23) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X23) | sK4 = X24 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) )),
% 2.29/0.66    inference(superposition,[],[f65,f574])).
% 2.29/0.66  fof(f62,plain,(
% 2.29/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.29/0.66    inference(definition_unfolding,[],[f41,f49])).
% 2.29/0.66  fof(f41,plain,(
% 2.29/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.29/0.66    inference(cnf_transformation,[],[f22])).
% 2.29/0.66  fof(f22,plain,(
% 2.29/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.29/0.66    inference(flattening,[],[f21])).
% 2.29/0.66  fof(f21,plain,(
% 2.29/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.29/0.66    inference(nnf_transformation,[],[f8])).
% 2.29/0.66  fof(f8,axiom,(
% 2.29/0.66    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 2.29/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 2.29/0.66  fof(f25,plain,(
% 2.29/0.66    k1_xboole_0 != sK1),
% 2.29/0.66    inference(cnf_transformation,[],[f18])).
% 2.29/0.66  fof(f24,plain,(
% 2.29/0.66    k1_xboole_0 != sK0),
% 2.29/0.66    inference(cnf_transformation,[],[f18])).
% 2.29/0.66  % SZS output end Proof for theBenchmark
% 2.29/0.66  % (6073)------------------------------
% 2.29/0.66  % (6073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.66  % (6073)Termination reason: Refutation
% 2.29/0.66  
% 2.29/0.66  % (6073)Memory used [KB]: 6908
% 2.29/0.66  % (6073)Time elapsed: 0.152 s
% 2.29/0.66  % (6073)------------------------------
% 2.29/0.66  % (6073)------------------------------
% 2.29/0.67  % (6050)Success in time 0.302 s
%------------------------------------------------------------------------------
