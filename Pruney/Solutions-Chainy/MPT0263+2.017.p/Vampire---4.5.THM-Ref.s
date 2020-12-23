%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:14 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 126 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 263 expanded)
%              Number of equality atoms :   60 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f66,f75,f102,f129])).

fof(f129,plain,
    ( ~ spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f123,f78])).

fof(f78,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl4_3 ),
    inference(superposition,[],[f74,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f74,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_3
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f123,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f92,f108])).

fof(f108,plain,
    ( sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f101,f50])).

fof(f50,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f101,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_4
  <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f92,plain,
    ( k2_enumset1(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f65,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ) ),
    inference(definition_unfolding,[],[f32,f39,f28,f39])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f65,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_2
  <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,
    ( spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f56,f52,f99])).

fof(f52,plain,
    ( spl4_1
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f56,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f54,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f54,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f75,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f24,f39,f28,f39])).

fof(f24,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f66,plain,
    ( spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f57,f52,f63])).

fof(f57,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f54,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f41,f52])).

fof(f41,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f23,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:44:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.36  ipcrm: permission denied for id (805437440)
% 0.21/0.36  ipcrm: permission denied for id (805470210)
% 0.21/0.37  ipcrm: permission denied for id (808288259)
% 0.21/0.37  ipcrm: permission denied for id (808386566)
% 0.21/0.37  ipcrm: permission denied for id (808419335)
% 0.21/0.37  ipcrm: permission denied for id (808452104)
% 0.21/0.37  ipcrm: permission denied for id (805535753)
% 0.21/0.37  ipcrm: permission denied for id (805568522)
% 0.21/0.38  ipcrm: permission denied for id (808484875)
% 0.21/0.38  ipcrm: permission denied for id (808517644)
% 0.21/0.38  ipcrm: permission denied for id (805634061)
% 0.21/0.38  ipcrm: permission denied for id (808550414)
% 0.21/0.38  ipcrm: permission denied for id (808583183)
% 0.21/0.38  ipcrm: permission denied for id (805699600)
% 0.21/0.38  ipcrm: permission denied for id (808615953)
% 0.21/0.39  ipcrm: permission denied for id (805797908)
% 0.21/0.39  ipcrm: permission denied for id (805830677)
% 0.21/0.39  ipcrm: permission denied for id (808714262)
% 0.21/0.39  ipcrm: permission denied for id (805896215)
% 0.21/0.39  ipcrm: permission denied for id (808779801)
% 0.21/0.39  ipcrm: permission denied for id (805961754)
% 0.21/0.40  ipcrm: permission denied for id (808878108)
% 0.21/0.40  ipcrm: permission denied for id (808943646)
% 0.21/0.40  ipcrm: permission denied for id (808976415)
% 0.21/0.40  ipcrm: permission denied for id (806158369)
% 0.21/0.40  ipcrm: permission denied for id (809041954)
% 0.21/0.41  ipcrm: permission denied for id (809074723)
% 0.21/0.41  ipcrm: permission denied for id (809107492)
% 0.21/0.41  ipcrm: permission denied for id (806223909)
% 0.21/0.41  ipcrm: permission denied for id (809173031)
% 0.21/0.41  ipcrm: permission denied for id (806289448)
% 0.21/0.41  ipcrm: permission denied for id (809205801)
% 0.21/0.42  ipcrm: permission denied for id (806354987)
% 0.21/0.42  ipcrm: permission denied for id (809271340)
% 0.21/0.42  ipcrm: permission denied for id (806453293)
% 0.21/0.42  ipcrm: permission denied for id (809304110)
% 0.21/0.42  ipcrm: permission denied for id (806420527)
% 0.21/0.42  ipcrm: permission denied for id (806518833)
% 0.21/0.43  ipcrm: permission denied for id (809402419)
% 0.21/0.43  ipcrm: permission denied for id (809435188)
% 0.21/0.43  ipcrm: permission denied for id (809500726)
% 0.21/0.43  ipcrm: permission denied for id (809533495)
% 0.21/0.43  ipcrm: permission denied for id (809599033)
% 0.21/0.44  ipcrm: permission denied for id (809631802)
% 0.21/0.44  ipcrm: permission denied for id (809697340)
% 0.21/0.44  ipcrm: permission denied for id (806780989)
% 0.21/0.44  ipcrm: permission denied for id (809795648)
% 0.21/0.44  ipcrm: permission denied for id (809828417)
% 0.21/0.44  ipcrm: permission denied for id (809861186)
% 0.21/0.45  ipcrm: permission denied for id (809893955)
% 0.21/0.45  ipcrm: permission denied for id (809926724)
% 0.21/0.45  ipcrm: permission denied for id (810057800)
% 0.21/0.46  ipcrm: permission denied for id (807043148)
% 0.21/0.46  ipcrm: permission denied for id (807075917)
% 0.21/0.46  ipcrm: permission denied for id (810221647)
% 0.21/0.46  ipcrm: permission denied for id (807206993)
% 0.21/0.47  ipcrm: permission denied for id (810287186)
% 0.21/0.47  ipcrm: permission denied for id (807272531)
% 0.21/0.47  ipcrm: permission denied for id (807305300)
% 0.21/0.47  ipcrm: permission denied for id (810319957)
% 0.21/0.47  ipcrm: permission denied for id (810352726)
% 0.21/0.47  ipcrm: permission denied for id (807403607)
% 0.21/0.48  ipcrm: permission denied for id (810516572)
% 0.21/0.48  ipcrm: permission denied for id (810582110)
% 0.21/0.48  ipcrm: permission denied for id (810614879)
% 0.21/0.48  ipcrm: permission denied for id (807501920)
% 0.21/0.48  ipcrm: permission denied for id (810647649)
% 0.21/0.49  ipcrm: permission denied for id (807534690)
% 0.21/0.49  ipcrm: permission denied for id (807567460)
% 0.21/0.49  ipcrm: permission denied for id (807632998)
% 0.21/0.49  ipcrm: permission denied for id (807665769)
% 0.21/0.50  ipcrm: permission denied for id (810811498)
% 0.21/0.50  ipcrm: permission denied for id (810942574)
% 0.21/0.50  ipcrm: permission denied for id (807862383)
% 0.21/0.50  ipcrm: permission denied for id (807927921)
% 0.21/0.51  ipcrm: permission denied for id (807960690)
% 0.21/0.51  ipcrm: permission denied for id (811008115)
% 0.21/0.51  ipcrm: permission denied for id (811040884)
% 0.21/0.51  ipcrm: permission denied for id (808026231)
% 0.21/0.52  ipcrm: permission denied for id (811204730)
% 0.21/0.52  ipcrm: permission denied for id (811237499)
% 0.21/0.52  ipcrm: permission denied for id (808124540)
% 0.21/0.52  ipcrm: permission denied for id (808222847)
% 0.68/0.65  % (32620)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.13/0.66  % (32628)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.67  % (32638)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.68  % (32638)Refutation found. Thanks to Tanya!
% 1.22/0.68  % SZS status Theorem for theBenchmark
% 1.22/0.68  % (32621)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.68  % (32644)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.69  % (32644)Refutation not found, incomplete strategy% (32644)------------------------------
% 1.22/0.69  % (32644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (32644)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (32644)Memory used [KB]: 6140
% 1.22/0.69  % (32644)Time elapsed: 0.130 s
% 1.22/0.69  % (32644)------------------------------
% 1.22/0.69  % (32644)------------------------------
% 1.22/0.69  % SZS output start Proof for theBenchmark
% 1.22/0.69  fof(f132,plain,(
% 1.22/0.69    $false),
% 1.22/0.69    inference(avatar_sat_refutation,[],[f55,f66,f75,f102,f129])).
% 1.22/0.69  fof(f129,plain,(
% 1.22/0.69    ~spl4_2 | spl4_3 | ~spl4_4),
% 1.22/0.69    inference(avatar_contradiction_clause,[],[f128])).
% 1.22/0.69  fof(f128,plain,(
% 1.22/0.69    $false | (~spl4_2 | spl4_3 | ~spl4_4)),
% 1.22/0.69    inference(subsumption_resolution,[],[f123,f78])).
% 1.22/0.69  fof(f78,plain,(
% 1.22/0.69    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl4_3),
% 1.22/0.69    inference(superposition,[],[f74,f42])).
% 1.22/0.69  fof(f42,plain,(
% 1.22/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.22/0.69    inference(definition_unfolding,[],[f26,f28,f28])).
% 1.22/0.69  fof(f28,plain,(
% 1.22/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.22/0.69    inference(cnf_transformation,[],[f3])).
% 1.22/0.69  fof(f3,axiom,(
% 1.22/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.22/0.69  fof(f26,plain,(
% 1.22/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f1])).
% 1.22/0.69  fof(f1,axiom,(
% 1.22/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.22/0.69  fof(f74,plain,(
% 1.22/0.69    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl4_3),
% 1.22/0.69    inference(avatar_component_clause,[],[f72])).
% 1.22/0.69  fof(f72,plain,(
% 1.22/0.69    spl4_3 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.22/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.22/0.69  fof(f123,plain,(
% 1.22/0.69    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | (~spl4_2 | ~spl4_4)),
% 1.22/0.69    inference(backward_demodulation,[],[f92,f108])).
% 1.22/0.69  fof(f108,plain,(
% 1.22/0.69    sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl4_4),
% 1.22/0.69    inference(unit_resulting_resolution,[],[f101,f50])).
% 1.22/0.69  fof(f50,plain,(
% 1.22/0.69    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.22/0.69    inference(equality_resolution,[],[f47])).
% 1.22/0.69  fof(f47,plain,(
% 1.22/0.69    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.22/0.69    inference(definition_unfolding,[],[f33,f39])).
% 1.22/0.69  fof(f39,plain,(
% 1.22/0.69    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.22/0.69    inference(definition_unfolding,[],[f25,f38])).
% 1.22/0.69  fof(f38,plain,(
% 1.22/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.22/0.69    inference(definition_unfolding,[],[f27,f37])).
% 1.22/0.69  fof(f37,plain,(
% 1.22/0.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f7])).
% 1.22/0.69  fof(f7,axiom,(
% 1.22/0.69    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.22/0.69  fof(f27,plain,(
% 1.22/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f6])).
% 1.22/0.69  fof(f6,axiom,(
% 1.22/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.22/0.69  fof(f25,plain,(
% 1.22/0.69    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f5])).
% 1.22/0.69  fof(f5,axiom,(
% 1.22/0.69    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.22/0.69  fof(f33,plain,(
% 1.22/0.69    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.22/0.69    inference(cnf_transformation,[],[f22])).
% 1.22/0.69  fof(f22,plain,(
% 1.22/0.69    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.22/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 1.22/0.69  fof(f21,plain,(
% 1.22/0.69    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.22/0.69    introduced(choice_axiom,[])).
% 1.22/0.69  fof(f20,plain,(
% 1.22/0.69    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.22/0.69    inference(rectify,[],[f19])).
% 1.22/0.69  fof(f19,plain,(
% 1.22/0.69    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.22/0.69    inference(nnf_transformation,[],[f4])).
% 1.22/0.69  fof(f4,axiom,(
% 1.22/0.69    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.22/0.69  fof(f101,plain,(
% 1.22/0.69    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_4),
% 1.22/0.69    inference(avatar_component_clause,[],[f99])).
% 1.22/0.69  fof(f99,plain,(
% 1.22/0.69    spl4_4 <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.22/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.22/0.69  fof(f92,plain,(
% 1.22/0.69    k2_enumset1(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) | ~spl4_2),
% 1.22/0.69    inference(unit_resulting_resolution,[],[f65,f43])).
% 1.22/0.69  fof(f43,plain,(
% 1.22/0.69    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) )),
% 1.22/0.69    inference(definition_unfolding,[],[f32,f39,f28,f39])).
% 1.22/0.69  fof(f32,plain,(
% 1.22/0.69    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f14])).
% 1.22/0.69  fof(f14,plain,(
% 1.22/0.69    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.22/0.69    inference(ennf_transformation,[],[f8])).
% 1.22/0.69  fof(f8,axiom,(
% 1.22/0.69    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.22/0.69  fof(f65,plain,(
% 1.22/0.69    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) | ~spl4_2),
% 1.22/0.69    inference(avatar_component_clause,[],[f63])).
% 1.22/0.69  fof(f63,plain,(
% 1.22/0.69    spl4_2 <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)),
% 1.22/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.22/0.69  fof(f102,plain,(
% 1.22/0.69    spl4_4 | spl4_1),
% 1.22/0.69    inference(avatar_split_clause,[],[f56,f52,f99])).
% 1.22/0.69  fof(f52,plain,(
% 1.22/0.69    spl4_1 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.22/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.22/0.69  fof(f56,plain,(
% 1.22/0.69    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | spl4_1),
% 1.22/0.69    inference(unit_resulting_resolution,[],[f54,f29])).
% 1.22/0.69  fof(f29,plain,(
% 1.22/0.69    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f18])).
% 1.22/0.69  fof(f18,plain,(
% 1.22/0.69    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.22/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f17])).
% 1.22/0.69  fof(f17,plain,(
% 1.22/0.69    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.22/0.69    introduced(choice_axiom,[])).
% 1.22/0.69  fof(f13,plain,(
% 1.22/0.69    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.22/0.69    inference(ennf_transformation,[],[f11])).
% 1.22/0.69  fof(f11,plain,(
% 1.22/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.22/0.69    inference(rectify,[],[f2])).
% 1.22/0.69  fof(f2,axiom,(
% 1.22/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.22/0.69  fof(f54,plain,(
% 1.22/0.69    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl4_1),
% 1.22/0.69    inference(avatar_component_clause,[],[f52])).
% 1.22/0.69  fof(f75,plain,(
% 1.22/0.69    ~spl4_3),
% 1.22/0.69    inference(avatar_split_clause,[],[f40,f72])).
% 1.22/0.69  fof(f40,plain,(
% 1.22/0.69    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.22/0.69    inference(definition_unfolding,[],[f24,f39,f28,f39])).
% 1.22/0.69  fof(f24,plain,(
% 1.22/0.69    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.22/0.69    inference(cnf_transformation,[],[f16])).
% 1.22/0.69  fof(f16,plain,(
% 1.22/0.69    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.22/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).
% 1.22/0.69  fof(f15,plain,(
% 1.22/0.69    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 1.22/0.69    introduced(choice_axiom,[])).
% 1.22/0.69  fof(f12,plain,(
% 1.22/0.69    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.22/0.69    inference(ennf_transformation,[],[f10])).
% 1.22/0.69  fof(f10,negated_conjecture,(
% 1.22/0.69    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 1.22/0.69    inference(negated_conjecture,[],[f9])).
% 1.22/0.69  fof(f9,conjecture,(
% 1.22/0.69    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 1.22/0.69  fof(f66,plain,(
% 1.22/0.69    spl4_2 | spl4_1),
% 1.22/0.69    inference(avatar_split_clause,[],[f57,f52,f63])).
% 1.22/0.69  fof(f57,plain,(
% 1.22/0.69    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) | spl4_1),
% 1.22/0.69    inference(unit_resulting_resolution,[],[f54,f30])).
% 1.22/0.69  fof(f30,plain,(
% 1.22/0.69    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f18])).
% 1.22/0.69  fof(f55,plain,(
% 1.22/0.69    ~spl4_1),
% 1.22/0.69    inference(avatar_split_clause,[],[f41,f52])).
% 1.22/0.69  fof(f41,plain,(
% 1.22/0.69    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.22/0.69    inference(definition_unfolding,[],[f23,f39])).
% 1.22/0.69  fof(f23,plain,(
% 1.22/0.69    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.22/0.69    inference(cnf_transformation,[],[f16])).
% 1.22/0.69  % SZS output end Proof for theBenchmark
% 1.22/0.69  % (32638)------------------------------
% 1.22/0.69  % (32638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (32638)Termination reason: Refutation
% 1.22/0.69  
% 1.22/0.69  % (32638)Memory used [KB]: 10746
% 1.22/0.69  % (32638)Time elapsed: 0.123 s
% 1.22/0.69  % (32638)------------------------------
% 1.22/0.69  % (32638)------------------------------
% 1.22/0.69  % (32636)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.22/0.69  % (32636)Refutation not found, incomplete strategy% (32636)------------------------------
% 1.22/0.69  % (32636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (32636)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (32636)Memory used [KB]: 1663
% 1.22/0.69  % (32636)Time elapsed: 0.120 s
% 1.22/0.69  % (32636)------------------------------
% 1.22/0.69  % (32636)------------------------------
% 1.22/0.69  % (32454)Success in time 0.333 s
%------------------------------------------------------------------------------
