%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:14 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 373 expanded)
%              Number of leaves         :    6 ( 110 expanded)
%              Depth                    :   20
%              Number of atoms          :  172 (1137 expanded)
%              Number of equality atoms :  171 (1136 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f905,plain,(
    $false ),
    inference(subsumption_resolution,[],[f861,f60])).

fof(f60,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f53,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f48,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
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
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f54,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X3) ),
    inference(superposition,[],[f49,f48])).

fof(f49,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f861,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f35,f836])).

fof(f836,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ),
    inference(subsumption_resolution,[],[f827,f756])).

fof(f756,plain,(
    ! [X0] :
      ( sK0 != sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(trivial_inequality_removal,[],[f755])).

fof(f755,plain,(
    ! [X0] :
      ( sK1 != sK1
      | sK0 != sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(superposition,[],[f362,f740])).

fof(f740,plain,(
    ! [X0] :
      ( sK1 = sK5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(equality_resolution,[],[f541])).

fof(f541,plain,(
    ! [X28,X26,X29,X27] :
      ( k2_zfmisc_1(k2_zfmisc_1(X27,X28),X29) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X26)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X26)
      | sK5 = X28 ) ),
    inference(superposition,[],[f46,f481])).

fof(f481,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    inference(equality_resolution,[],[f324])).

fof(f324,plain,(
    ! [X6,X8,X7] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)
      | k2_zfmisc_1(sK4,sK5) = X6 ) ),
    inference(subsumption_resolution,[],[f304,f35])).

fof(f304,plain,(
    ! [X6,X8,X7] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k2_zfmisc_1(sK4,sK5) = X6 ) ),
    inference(superposition,[],[f47,f274])).

fof(f274,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) ),
    inference(backward_demodulation,[],[f36,f266])).

fof(f266,plain,(
    sK3 = sK7 ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,(
    ! [X19,X20,X18] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20)
      | sK7 = X20 ) ),
    inference(subsumption_resolution,[],[f157,f35])).

fof(f157,plain,(
    ! [X19,X20,X18] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK7 = X20 ) ),
    inference(superposition,[],[f45,f36])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f33,f21,f21,f21])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f36,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f18,f34,f34])).

fof(f18,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
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
      & k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f31,f21,f21,f21])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f32,f21,f21,f21])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f362,plain,
    ( sK1 != sK5
    | sK0 != sK4 ),
    inference(subsumption_resolution,[],[f361,f266])).

fof(f361,plain,
    ( sK3 != sK7
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f354])).

fof(f354,plain,
    ( sK2 != sK2
    | sK3 != sK7
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(backward_demodulation,[],[f20,f346])).

fof(f346,plain,(
    sK2 = sK6 ),
    inference(equality_resolution,[],[f230])).

fof(f230,plain,(
    ! [X6,X8,X7] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)
      | sK6 = X7 ) ),
    inference(subsumption_resolution,[],[f213,f35])).

fof(f213,plain,(
    ! [X6,X8,X7] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK6 = X7 ) ),
    inference(superposition,[],[f46,f36])).

fof(f20,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f15])).

fof(f827,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
      | sK0 = sK4 ) ),
    inference(equality_resolution,[],[f543])).

fof(f543,plain,(
    ! [X37,X35,X36,X34] :
      ( k2_zfmisc_1(k2_zfmisc_1(X35,X36),X37) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X34)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X34)
      | sK4 = X35 ) ),
    inference(superposition,[],[f47,f481])).

fof(f35,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f19,f34])).

fof(f19,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (28974)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (28966)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (28969)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (28962)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (28963)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.46/0.55  % (28986)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.46/0.56  % (28973)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.46/0.56  % (28981)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.46/0.56  % (28961)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.46/0.56  % (28970)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.56  % (28973)Refutation not found, incomplete strategy% (28973)------------------------------
% 1.46/0.56  % (28973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (28973)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (28973)Memory used [KB]: 1663
% 1.46/0.56  % (28973)Time elapsed: 0.090 s
% 1.46/0.56  % (28973)------------------------------
% 1.46/0.56  % (28973)------------------------------
% 1.46/0.56  % (28978)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.57  % (28982)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.46/0.57  % (28965)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.57  % (28987)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.57  % (28968)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.57  % (28985)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.46/0.57  % (28964)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.46/0.57  % (28985)Refutation not found, incomplete strategy% (28985)------------------------------
% 1.46/0.57  % (28985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (28985)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (28985)Memory used [KB]: 6268
% 1.46/0.57  % (28985)Time elapsed: 0.170 s
% 1.46/0.57  % (28985)------------------------------
% 1.46/0.57  % (28985)------------------------------
% 1.63/0.58  % (28979)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.63/0.58  % (28977)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.58  % (28977)Refutation not found, incomplete strategy% (28977)------------------------------
% 1.63/0.58  % (28977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (28977)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (28977)Memory used [KB]: 1663
% 1.63/0.58  % (28977)Time elapsed: 0.171 s
% 1.63/0.58  % (28977)------------------------------
% 1.63/0.58  % (28977)------------------------------
% 1.63/0.58  % (28971)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.63/0.58  % (28971)Refutation not found, incomplete strategy% (28971)------------------------------
% 1.63/0.58  % (28971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (28971)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (28971)Memory used [KB]: 10618
% 1.63/0.58  % (28971)Time elapsed: 0.164 s
% 1.63/0.58  % (28971)------------------------------
% 1.63/0.58  % (28971)------------------------------
% 1.63/0.59  % (28960)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.63/0.60  % (28960)Refutation not found, incomplete strategy% (28960)------------------------------
% 1.63/0.60  % (28960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (28960)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.60  
% 1.63/0.60  % (28960)Memory used [KB]: 1663
% 1.63/0.60  % (28960)Time elapsed: 0.172 s
% 1.63/0.60  % (28960)------------------------------
% 1.63/0.60  % (28960)------------------------------
% 1.63/0.60  % (28959)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.63/0.60  % (28984)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.63/0.61  % (28988)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.63/0.61  % (28988)Refutation not found, incomplete strategy% (28988)------------------------------
% 1.63/0.61  % (28988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.61  % (28988)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.61  
% 1.63/0.61  % (28988)Memory used [KB]: 1663
% 1.63/0.61  % (28988)Time elapsed: 0.183 s
% 1.63/0.61  % (28988)------------------------------
% 1.63/0.61  % (28988)------------------------------
% 1.63/0.61  % (28980)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.63/0.62  % (28972)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.63/0.62  % (28976)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.62  % (28983)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.63/0.62  % (28981)Refutation found. Thanks to Tanya!
% 1.63/0.62  % SZS status Theorem for theBenchmark
% 1.63/0.62  % SZS output start Proof for theBenchmark
% 1.63/0.63  fof(f905,plain,(
% 1.63/0.63    $false),
% 1.63/0.63    inference(subsumption_resolution,[],[f861,f60])).
% 1.63/0.63  fof(f60,plain,(
% 1.63/0.63    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.63/0.63    inference(forward_demodulation,[],[f54,f53])).
% 1.63/0.63  fof(f53,plain,(
% 1.63/0.63    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.63/0.63    inference(superposition,[],[f48,f48])).
% 1.63/0.63  fof(f48,plain,(
% 1.63/0.63    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 1.63/0.63    inference(equality_resolution,[],[f37])).
% 1.63/0.63  fof(f37,plain,(
% 1.63/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.63/0.63    inference(definition_unfolding,[],[f27,f34])).
% 1.63/0.63  fof(f34,plain,(
% 1.63/0.63    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.63/0.63    inference(definition_unfolding,[],[f22,f21])).
% 1.63/0.63  fof(f21,plain,(
% 1.63/0.63    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.63/0.63    inference(cnf_transformation,[],[f1])).
% 1.63/0.63  fof(f1,axiom,(
% 1.63/0.63    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.63/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.63/0.63  fof(f22,plain,(
% 1.63/0.63    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.63/0.63    inference(cnf_transformation,[],[f2])).
% 1.63/0.63  fof(f2,axiom,(
% 1.63/0.63    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.63/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.63/0.63  fof(f27,plain,(
% 1.63/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 1.63/0.63    inference(cnf_transformation,[],[f17])).
% 1.63/0.63  fof(f17,plain,(
% 1.63/0.63    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.63/0.63    inference(flattening,[],[f16])).
% 1.63/0.63  fof(f16,plain,(
% 1.63/0.63    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.63/0.63    inference(nnf_transformation,[],[f5])).
% 1.63/0.63  fof(f5,axiom,(
% 1.63/0.63    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 1.63/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.63/0.63  fof(f54,plain,(
% 1.63/0.63    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X3)) )),
% 1.63/0.63    inference(superposition,[],[f49,f48])).
% 1.63/0.63  fof(f49,plain,(
% 1.63/0.63    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 1.63/0.63    inference(equality_resolution,[],[f38])).
% 1.63/0.63  fof(f38,plain,(
% 1.63/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.63/0.63    inference(definition_unfolding,[],[f26,f34])).
% 1.63/0.63  fof(f26,plain,(
% 1.63/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 1.63/0.63    inference(cnf_transformation,[],[f17])).
% 1.63/0.63  fof(f861,plain,(
% 1.63/0.63    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)),
% 1.63/0.63    inference(backward_demodulation,[],[f35,f836])).
% 1.63/0.63  fof(f836,plain,(
% 1.63/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.63/0.63    inference(subsumption_resolution,[],[f827,f756])).
% 1.63/0.63  fof(f756,plain,(
% 1.63/0.63    ( ! [X0] : (sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.63/0.63    inference(trivial_inequality_removal,[],[f755])).
% 1.63/0.63  fof(f755,plain,(
% 1.63/0.63    ( ! [X0] : (sK1 != sK1 | sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.63/0.63    inference(superposition,[],[f362,f740])).
% 1.63/0.63  fof(f740,plain,(
% 1.63/0.63    ( ! [X0] : (sK1 = sK5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.63/0.63    inference(equality_resolution,[],[f541])).
% 1.63/0.63  fof(f541,plain,(
% 1.63/0.63    ( ! [X28,X26,X29,X27] : (k2_zfmisc_1(k2_zfmisc_1(X27,X28),X29) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X26) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X26) | sK5 = X28) )),
% 1.63/0.63    inference(superposition,[],[f46,f481])).
% 1.63/0.63  fof(f481,plain,(
% 1.63/0.63    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 1.63/0.63    inference(equality_resolution,[],[f324])).
% 1.63/0.63  fof(f324,plain,(
% 1.63/0.63    ( ! [X6,X8,X7] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8) | k2_zfmisc_1(sK4,sK5) = X6) )),
% 1.63/0.63    inference(subsumption_resolution,[],[f304,f35])).
% 1.63/0.63  fof(f304,plain,(
% 1.63/0.63    ( ! [X6,X8,X7] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK4,sK5) = X6) )),
% 1.63/0.63    inference(superposition,[],[f47,f274])).
% 1.63/0.63  fof(f274,plain,(
% 1.63/0.63    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)),
% 1.63/0.63    inference(backward_demodulation,[],[f36,f266])).
% 1.63/0.63  fof(f266,plain,(
% 1.63/0.63    sK3 = sK7),
% 1.63/0.63    inference(equality_resolution,[],[f175])).
% 1.63/0.63  fof(f175,plain,(
% 1.63/0.63    ( ! [X19,X20,X18] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) | sK7 = X20) )),
% 1.63/0.63    inference(subsumption_resolution,[],[f157,f35])).
% 1.63/0.63  fof(f157,plain,(
% 1.63/0.63    ( ! [X19,X20,X18] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK7 = X20) )),
% 1.63/0.63    inference(superposition,[],[f45,f36])).
% 1.63/0.63  fof(f45,plain,(
% 1.63/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | X2 = X5) )),
% 1.63/0.63    inference(definition_unfolding,[],[f33,f21,f21,f21])).
% 1.63/0.63  fof(f33,plain,(
% 1.63/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 1.63/0.63    inference(cnf_transformation,[],[f13])).
% 1.63/0.63  fof(f13,plain,(
% 1.63/0.63    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.63/0.63    inference(flattening,[],[f12])).
% 1.63/0.63  fof(f12,plain,(
% 1.63/0.63    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.63/0.63    inference(ennf_transformation,[],[f4])).
% 1.63/0.63  fof(f4,axiom,(
% 1.63/0.63    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0))),
% 1.63/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).
% 1.63/0.63  fof(f36,plain,(
% 1.63/0.63    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.63/0.63    inference(definition_unfolding,[],[f18,f34,f34])).
% 1.63/0.63  fof(f18,plain,(
% 1.63/0.63    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.63/0.63    inference(cnf_transformation,[],[f15])).
% 1.63/0.63  fof(f15,plain,(
% 1.63/0.63    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.63/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f14])).
% 1.63/0.63  fof(f14,plain,(
% 1.63/0.63    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.63/0.63    introduced(choice_axiom,[])).
% 1.63/0.63  fof(f9,plain,(
% 1.63/0.63    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.63/0.63    inference(flattening,[],[f8])).
% 1.63/0.63  fof(f8,plain,(
% 1.63/0.63    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.63/0.63    inference(ennf_transformation,[],[f7])).
% 1.63/0.63  fof(f7,negated_conjecture,(
% 1.63/0.63    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0))),
% 1.63/0.63    inference(negated_conjecture,[],[f6])).
% 1.63/0.63  fof(f6,conjecture,(
% 1.63/0.63    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0))),
% 1.63/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).
% 1.63/0.63  fof(f47,plain,(
% 1.63/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | X0 = X3) )),
% 1.63/0.63    inference(definition_unfolding,[],[f31,f21,f21,f21])).
% 1.63/0.63  fof(f31,plain,(
% 1.63/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 1.63/0.63    inference(cnf_transformation,[],[f13])).
% 1.63/0.63  fof(f46,plain,(
% 1.63/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | X1 = X4) )),
% 1.63/0.63    inference(definition_unfolding,[],[f32,f21,f21,f21])).
% 1.63/0.63  fof(f32,plain,(
% 1.63/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 1.63/0.63    inference(cnf_transformation,[],[f13])).
% 1.63/0.63  fof(f362,plain,(
% 1.63/0.63    sK1 != sK5 | sK0 != sK4),
% 1.63/0.63    inference(subsumption_resolution,[],[f361,f266])).
% 1.63/0.63  fof(f361,plain,(
% 1.63/0.63    sK3 != sK7 | sK1 != sK5 | sK0 != sK4),
% 1.63/0.63    inference(trivial_inequality_removal,[],[f354])).
% 1.63/0.63  fof(f354,plain,(
% 1.63/0.63    sK2 != sK2 | sK3 != sK7 | sK1 != sK5 | sK0 != sK4),
% 1.63/0.63    inference(backward_demodulation,[],[f20,f346])).
% 1.63/0.63  fof(f346,plain,(
% 1.63/0.63    sK2 = sK6),
% 1.63/0.63    inference(equality_resolution,[],[f230])).
% 1.63/0.63  fof(f230,plain,(
% 1.63/0.63    ( ! [X6,X8,X7] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8) | sK6 = X7) )),
% 1.63/0.63    inference(subsumption_resolution,[],[f213,f35])).
% 1.63/0.63  fof(f213,plain,(
% 1.63/0.63    ( ! [X6,X8,X7] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X7) )),
% 1.63/0.63    inference(superposition,[],[f46,f36])).
% 1.63/0.63  fof(f20,plain,(
% 1.63/0.63    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 1.63/0.63    inference(cnf_transformation,[],[f15])).
% 1.63/0.63  fof(f827,plain,(
% 1.63/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) | sK0 = sK4) )),
% 1.63/0.63    inference(equality_resolution,[],[f543])).
% 1.63/0.63  fof(f543,plain,(
% 1.63/0.63    ( ! [X37,X35,X36,X34] : (k2_zfmisc_1(k2_zfmisc_1(X35,X36),X37) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X34) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X34) | sK4 = X35) )),
% 1.63/0.63    inference(superposition,[],[f47,f481])).
% 1.63/0.63  fof(f35,plain,(
% 1.63/0.63    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 1.63/0.63    inference(definition_unfolding,[],[f19,f34])).
% 1.63/0.63  fof(f19,plain,(
% 1.63/0.63    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 1.63/0.63    inference(cnf_transformation,[],[f15])).
% 1.63/0.63  % SZS output end Proof for theBenchmark
% 1.63/0.63  % (28981)------------------------------
% 1.63/0.63  % (28981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.63  % (28981)Termination reason: Refutation
% 1.63/0.63  
% 1.63/0.63  % (28981)Memory used [KB]: 6524
% 1.63/0.63  % (28981)Time elapsed: 0.151 s
% 1.63/0.63  % (28981)------------------------------
% 1.63/0.63  % (28981)------------------------------
% 1.63/0.63  % (28958)Success in time 0.265 s
%------------------------------------------------------------------------------
