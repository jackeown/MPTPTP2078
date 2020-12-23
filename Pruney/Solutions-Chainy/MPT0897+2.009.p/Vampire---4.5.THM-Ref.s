%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:14 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 401 expanded)
%              Number of leaves         :    6 ( 116 expanded)
%              Depth                    :   20
%              Number of atoms          :  189 (1207 expanded)
%              Number of equality atoms :  188 (1206 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f444])).

fof(f444,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f325,f441])).

fof(f441,plain,(
    sK0 = sK4 ),
    inference(trivial_inequality_removal,[],[f440])).

fof(f440,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK4 ),
    inference(duplicate_literal_removal,[],[f439])).

fof(f439,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK4
    | sK0 = sK4 ),
    inference(superposition,[],[f395,f391])).

fof(f391,plain,(
    ! [X38] :
      ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X38)
      | sK0 = sK4 ) ),
    inference(superposition,[],[f41,f376])).

fof(f376,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
      | sK0 = sK4 ) ),
    inference(equality_resolution,[],[f231])).

fof(f231,plain,(
    ! [X21,X19,X20,X18] :
      ( k2_zfmisc_1(k2_zfmisc_1(X19,X20),X21) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X18)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X18)
      | sK4 = X19 ) ),
    inference(superposition,[],[f39,f224])).

fof(f224,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    inference(trivial_inequality_removal,[],[f202])).

fof(f202,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    inference(superposition,[],[f30,f200])).

fof(f200,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X17,X18,X16] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18)
      | k2_zfmisc_1(sK4,sK5) = X16 ) ),
    inference(superposition,[],[f39,f31])).

fof(f31,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f16,f29,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f30,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f17,f29])).

fof(f17,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f26,f25,f25,f25])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f41,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f395,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | sK0 = sK4 ),
    inference(superposition,[],[f30,f376])).

fof(f325,plain,(
    sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f324])).

fof(f324,plain,
    ( sK1 != sK1
    | sK0 != sK4 ),
    inference(superposition,[],[f164,f319])).

fof(f319,plain,(
    sK1 = sK5 ),
    inference(trivial_inequality_removal,[],[f318])).

fof(f318,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = sK5 ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = sK5
    | sK1 = sK5 ),
    inference(superposition,[],[f276,f272])).

fof(f272,plain,(
    ! [X35] :
      ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X35)
      | sK1 = sK5 ) ),
    inference(superposition,[],[f41,f259])).

fof(f259,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
      | sK1 = sK5 ) ),
    inference(equality_resolution,[],[f229])).

fof(f229,plain,(
    ! [X12,X10,X13,X11] :
      ( k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10)
      | sK5 = X12 ) ),
    inference(superposition,[],[f38,f224])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f27,f25,f25,f25])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f276,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | sK1 = sK5 ),
    inference(superposition,[],[f30,f259])).

fof(f164,plain,
    ( sK1 != sK5
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( sK2 != sK2
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(superposition,[],[f114,f158])).

fof(f158,plain,(
    sK2 = sK6 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK2 = sK6 ),
    inference(superposition,[],[f30,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | sK2 = sK6 ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X12,X10,X11] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12)
      | sK6 = X11 ) ),
    inference(superposition,[],[f38,f31])).

fof(f114,plain,
    ( sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( sK3 != sK3
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(superposition,[],[f18,f96])).

fof(f96,plain,(
    sK3 = sK7 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK3 = sK7 ),
    inference(superposition,[],[f30,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | sK3 = sK7 ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X4,X5] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)
      | sK7 = X6 ) ),
    inference(superposition,[],[f37,f31])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f28,f25,f25,f25])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:39:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.48  % (28837)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (28846)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (28846)Refutation not found, incomplete strategy% (28846)------------------------------
% 0.21/0.50  % (28846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28846)Memory used [KB]: 10618
% 0.21/0.50  % (28846)Time elapsed: 0.079 s
% 0.21/0.50  % (28846)------------------------------
% 0.21/0.50  % (28846)------------------------------
% 0.21/0.52  % (28836)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (28832)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (28835)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (28838)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (28844)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (28856)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (28863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (28847)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (28842)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (28845)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (28841)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (28848)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (28864)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (28848)Refutation not found, incomplete strategy% (28848)------------------------------
% 0.21/0.54  % (28848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28848)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28848)Memory used [KB]: 1663
% 0.21/0.54  % (28848)Time elapsed: 0.095 s
% 0.21/0.54  % (28848)------------------------------
% 0.21/0.54  % (28848)------------------------------
% 0.21/0.54  % (28833)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (28843)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (28864)Refutation not found, incomplete strategy% (28864)------------------------------
% 0.21/0.54  % (28864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28864)Memory used [KB]: 1663
% 0.21/0.54  % (28864)Time elapsed: 0.133 s
% 0.21/0.54  % (28864)------------------------------
% 0.21/0.54  % (28864)------------------------------
% 0.21/0.54  % (28857)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (28861)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (28862)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (28858)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (28853)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (28849)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (28860)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (28840)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (28851)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (28852)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (28855)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.49/0.56  % (28833)Refutation found. Thanks to Tanya!
% 1.49/0.56  % SZS status Theorem for theBenchmark
% 1.49/0.56  % (28859)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.49/0.56  % (28852)Refutation not found, incomplete strategy% (28852)------------------------------
% 1.49/0.56  % (28852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (28852)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (28852)Memory used [KB]: 1663
% 1.49/0.56  % (28852)Time elapsed: 0.149 s
% 1.49/0.56  % (28852)------------------------------
% 1.49/0.56  % (28852)------------------------------
% 1.49/0.56  % (28850)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.56  % (28861)Refutation not found, incomplete strategy% (28861)------------------------------
% 1.49/0.56  % (28861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (28861)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (28861)Memory used [KB]: 6268
% 1.49/0.56  % (28861)Time elapsed: 0.150 s
% 1.49/0.56  % (28861)------------------------------
% 1.49/0.56  % (28861)------------------------------
% 1.49/0.56  % (28850)Refutation not found, incomplete strategy% (28850)------------------------------
% 1.49/0.56  % (28850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (28850)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (28850)Memory used [KB]: 10618
% 1.49/0.56  % (28850)Time elapsed: 0.150 s
% 1.49/0.56  % (28850)------------------------------
% 1.49/0.56  % (28850)------------------------------
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f445,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f444])).
% 1.56/0.57  fof(f444,plain,(
% 1.56/0.57    sK0 != sK0),
% 1.56/0.57    inference(superposition,[],[f325,f441])).
% 1.56/0.57  fof(f441,plain,(
% 1.56/0.57    sK0 = sK4),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f440])).
% 1.56/0.57  fof(f440,plain,(
% 1.56/0.57    k1_xboole_0 != k1_xboole_0 | sK0 = sK4),
% 1.56/0.57    inference(duplicate_literal_removal,[],[f439])).
% 1.56/0.57  fof(f439,plain,(
% 1.56/0.57    k1_xboole_0 != k1_xboole_0 | sK0 = sK4 | sK0 = sK4),
% 1.56/0.57    inference(superposition,[],[f395,f391])).
% 1.56/0.57  fof(f391,plain,(
% 1.56/0.57    ( ! [X38] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X38) | sK0 = sK4) )),
% 1.56/0.57    inference(superposition,[],[f41,f376])).
% 1.56/0.57  fof(f376,plain,(
% 1.56/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) | sK0 = sK4) )),
% 1.56/0.57    inference(equality_resolution,[],[f231])).
% 1.56/0.57  fof(f231,plain,(
% 1.56/0.57    ( ! [X21,X19,X20,X18] : (k2_zfmisc_1(k2_zfmisc_1(X19,X20),X21) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X18) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X18) | sK4 = X19) )),
% 1.56/0.57    inference(superposition,[],[f39,f224])).
% 1.56/0.57  fof(f224,plain,(
% 1.56/0.57    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f202])).
% 1.56/0.57  fof(f202,plain,(
% 1.56/0.57    k1_xboole_0 != k1_xboole_0 | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 1.56/0.57    inference(superposition,[],[f30,f200])).
% 1.56/0.57  fof(f200,plain,(
% 1.56/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 1.56/0.57    inference(equality_resolution,[],[f50])).
% 1.56/0.57  fof(f50,plain,(
% 1.56/0.57    ( ! [X17,X18,X16] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) | k2_zfmisc_1(sK4,sK5) = X16) )),
% 1.56/0.57    inference(superposition,[],[f39,f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.56/0.57    inference(definition_unfolding,[],[f16,f29,f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f24,f25])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f2])).
% 1.56/0.57  fof(f2,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.56/0.57    inference(cnf_transformation,[],[f13])).
% 1.56/0.57  fof(f13,plain,(
% 1.56/0.57    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f12])).
% 1.56/0.57  fof(f12,plain,(
% 1.56/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f9,plain,(
% 1.56/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.56/0.57    inference(flattening,[],[f8])).
% 1.56/0.57  fof(f8,plain,(
% 1.56/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.56/0.57    inference(ennf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.56/0.57    inference(negated_conjecture,[],[f6])).
% 1.56/0.57  fof(f6,conjecture,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 1.56/0.57    inference(definition_unfolding,[],[f17,f29])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 1.56/0.57    inference(cnf_transformation,[],[f13])).
% 1.56/0.57  fof(f39,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X0 = X3) )),
% 1.56/0.57    inference(definition_unfolding,[],[f26,f25,f25,f25])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f11])).
% 1.56/0.57  fof(f11,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.56/0.57    inference(flattening,[],[f10])).
% 1.56/0.57  fof(f10,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.56/0.57    inference(ennf_transformation,[],[f4])).
% 1.56/0.57  fof(f4,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 1.56/0.57  fof(f41,plain,(
% 1.56/0.57    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 1.56/0.57    inference(equality_resolution,[],[f33])).
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f22,f29])).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.56/0.57    inference(flattening,[],[f14])).
% 1.56/0.57  fof(f14,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.56/0.57    inference(nnf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.56/0.57  fof(f395,plain,(
% 1.56/0.57    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | sK0 = sK4),
% 1.56/0.57    inference(superposition,[],[f30,f376])).
% 1.56/0.57  fof(f325,plain,(
% 1.56/0.57    sK0 != sK4),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f324])).
% 1.56/0.57  fof(f324,plain,(
% 1.56/0.57    sK1 != sK1 | sK0 != sK4),
% 1.56/0.57    inference(superposition,[],[f164,f319])).
% 1.56/0.57  fof(f319,plain,(
% 1.56/0.57    sK1 = sK5),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f318])).
% 1.56/0.57  fof(f318,plain,(
% 1.56/0.57    k1_xboole_0 != k1_xboole_0 | sK1 = sK5),
% 1.56/0.57    inference(duplicate_literal_removal,[],[f317])).
% 1.56/0.57  fof(f317,plain,(
% 1.56/0.57    k1_xboole_0 != k1_xboole_0 | sK1 = sK5 | sK1 = sK5),
% 1.56/0.57    inference(superposition,[],[f276,f272])).
% 1.56/0.57  fof(f272,plain,(
% 1.56/0.57    ( ! [X35] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X35) | sK1 = sK5) )),
% 1.56/0.57    inference(superposition,[],[f41,f259])).
% 1.56/0.57  fof(f259,plain,(
% 1.56/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) | sK1 = sK5) )),
% 1.56/0.57    inference(equality_resolution,[],[f229])).
% 1.56/0.57  fof(f229,plain,(
% 1.56/0.57    ( ! [X12,X10,X13,X11] : (k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10) | sK5 = X12) )),
% 1.56/0.57    inference(superposition,[],[f38,f224])).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X1 = X4) )),
% 1.56/0.57    inference(definition_unfolding,[],[f27,f25,f25,f25])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f11])).
% 1.56/0.57  fof(f276,plain,(
% 1.56/0.57    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | sK1 = sK5),
% 1.56/0.57    inference(superposition,[],[f30,f259])).
% 1.56/0.57  fof(f164,plain,(
% 1.56/0.57    sK1 != sK5 | sK0 != sK4),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f163])).
% 1.56/0.57  fof(f163,plain,(
% 1.56/0.57    sK2 != sK2 | sK1 != sK5 | sK0 != sK4),
% 1.56/0.57    inference(superposition,[],[f114,f158])).
% 1.56/0.57  fof(f158,plain,(
% 1.56/0.57    sK2 = sK6),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f136])).
% 1.56/0.57  fof(f136,plain,(
% 1.56/0.57    k1_xboole_0 != k1_xboole_0 | sK2 = sK6),
% 1.56/0.57    inference(superposition,[],[f30,f110])).
% 1.56/0.57  fof(f110,plain,(
% 1.56/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK2 = sK6),
% 1.56/0.57    inference(equality_resolution,[],[f48])).
% 1.56/0.57  fof(f48,plain,(
% 1.56/0.57    ( ! [X12,X10,X11] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) | sK6 = X11) )),
% 1.56/0.57    inference(superposition,[],[f38,f31])).
% 1.56/0.57  fof(f114,plain,(
% 1.56/0.57    sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f113])).
% 1.56/0.57  fof(f113,plain,(
% 1.56/0.57    sK3 != sK3 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 1.56/0.57    inference(superposition,[],[f18,f96])).
% 1.56/0.57  fof(f96,plain,(
% 1.56/0.57    sK3 = sK7),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f74])).
% 1.56/0.57  fof(f74,plain,(
% 1.56/0.57    k1_xboole_0 != k1_xboole_0 | sK3 = sK7),
% 1.56/0.57    inference(superposition,[],[f30,f72])).
% 1.56/0.57  fof(f72,plain,(
% 1.56/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK3 = sK7),
% 1.56/0.57    inference(equality_resolution,[],[f46])).
% 1.56/0.57  fof(f46,plain,(
% 1.56/0.57    ( ! [X6,X4,X5] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6) | sK7 = X6) )),
% 1.56/0.57    inference(superposition,[],[f37,f31])).
% 1.56/0.57  fof(f37,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X2 = X5) )),
% 1.56/0.57    inference(definition_unfolding,[],[f28,f25,f25,f25])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f11])).
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 1.56/0.57    inference(cnf_transformation,[],[f13])).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (28833)------------------------------
% 1.56/0.57  % (28833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (28833)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (28833)Memory used [KB]: 1918
% 1.56/0.57  % (28833)Time elapsed: 0.145 s
% 1.56/0.57  % (28833)------------------------------
% 1.56/0.57  % (28833)------------------------------
% 1.56/0.58  % (28830)Success in time 0.206 s
%------------------------------------------------------------------------------
