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
% DateTime   : Thu Dec  3 12:41:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 614 expanded)
%              Number of leaves         :   16 ( 191 expanded)
%              Depth                    :   12
%              Number of atoms          :  298 (1586 expanded)
%              Number of equality atoms :   32 ( 216 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f214,f287,f387,f547,f563,f579,f635,f770,f830,f918,f1024,f1293])).

fof(f1293,plain,
    ( ~ spl8_5
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f1284])).

fof(f1284,plain,
    ( $false
    | ~ spl8_5
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f1218,f624,f1130,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r2_hidden(sK6(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f1130,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,sK1))
    | ~ spl8_5
    | spl8_7 ),
    inference(backward_demodulation,[],[f1074,f1113])).

fof(f1113,plain,
    ( sK1 = sK2
    | ~ spl8_5
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f533,f624,f24])).

fof(f533,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl8_5
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1074,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,sK2))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f32,f533,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f624,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f549,f558,f115])).

fof(f115,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f16,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f16,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(X0,X1)
      & ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
          <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
       => k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
     => k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_zfmisc_1)).

fof(f558,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK7(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f550,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f550,plain,
    ( ~ r2_hidden(sK7(sK0,sK2),sK2)
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f546,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f546,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl8_7
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f549,plain,
    ( r2_hidden(sK7(sK0,sK2),sK0)
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f546,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1218,plain,
    ( sK1 != k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5
    | spl8_7 ),
    inference(backward_demodulation,[],[f1122,f1210])).

fof(f1210,plain,
    ( ! [X0] : sK1 = k2_zfmisc_1(sK1,X0)
    | ~ spl8_5
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f624,f1129,f24])).

fof(f1129,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(sK1,X1))
    | ~ spl8_5
    | spl8_7 ),
    inference(backward_demodulation,[],[f1072,f1113])).

fof(f1072,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(sK2,X1))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f32,f533,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1122,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK1,sK3)
    | ~ spl8_5
    | spl8_7 ),
    inference(backward_demodulation,[],[f17,f1113])).

fof(f17,plain,(
    k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f1024,plain,
    ( ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f1016])).

fof(f1016,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f833,f972,f972,f24])).

fof(f972,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,X1))
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f32,f962,f18])).

fof(f962,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f533,f542])).

fof(f542,plain,
    ( sK0 = sK2
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl8_6
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f833,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK3)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f17,f542])).

fof(f918,plain,
    ( ~ spl8_6
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f910])).

fof(f910,plain,
    ( $false
    | ~ spl8_6
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f833,f847,f847,f24])).

fof(f847,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,X1))
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f32,f627,f18])).

fof(f627,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f580,f595,f115])).

fof(f595,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK7(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f581,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f581,plain,
    ( ~ r2_hidden(sK7(sK1,sK3),sK3)
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f578,f31])).

fof(f578,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl8_10
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f580,plain,
    ( r2_hidden(sK7(sK1,sK3),sK1)
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f578,f30])).

fof(f830,plain,
    ( ~ spl8_6
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f829])).

fof(f829,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(trivial_inequality_removal,[],[f826])).

fof(f826,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1)
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f638,f542])).

fof(f638,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK1)
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f17,f574])).

fof(f574,plain,
    ( sK1 = sK3
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f572])).

fof(f572,plain,
    ( spl8_9
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f770,plain,
    ( spl8_7
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | spl8_7
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f638,f656,f656,f24])).

fof(f656,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,sK1))
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f32,f624,f19])).

fof(f635,plain,
    ( spl8_7
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | spl8_7
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f549,f580,f595,f115])).

fof(f579,plain,
    ( spl8_9
    | ~ spl8_10
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f570,f561,f576,f572])).

fof(f561,plain,
    ( spl8_8
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK3)
        | r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f570,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK1 = sK3
    | ~ spl8_8 ),
    inference(resolution,[],[f568,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f568,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f567])).

fof(f567,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl8_8 ),
    inference(resolution,[],[f565,f30])).

fof(f565,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK7(X1,sK1),sK3)
        | r1_tarski(X1,sK1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f562,f31])).

fof(f562,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(X2,sK3) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f561])).

fof(f563,plain,
    ( spl8_5
    | spl8_8 ),
    inference(avatar_split_clause,[],[f36,f561,f532])).

fof(f36,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK3)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f34,f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f15,f28])).

fof(f15,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f547,plain,
    ( spl8_6
    | ~ spl8_7
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f538,f38,f544,f540])).

fof(f38,plain,
    ( spl8_1
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f538,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl8_1 ),
    inference(resolution,[],[f536,f23])).

fof(f536,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl8_1 ),
    inference(duplicate_literal_removal,[],[f535])).

fof(f535,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f516,f30])).

fof(f516,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK7(X1,sK0),sK2)
        | r1_tarski(X1,sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f39,f31])).

fof(f39,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f387,plain,
    ( ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f213,f365,f30])).

fof(f365,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f354,f349])).

fof(f349,plain,
    ( ! [X0] : sK1 = k2_zfmisc_1(X0,sK1)
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f132,f336])).

fof(f336,plain,
    ( sK1 = sK3
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f42,f213,f24])).

fof(f42,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl8_2
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f132,plain,
    ( ! [X0] : sK3 = k2_zfmisc_1(X0,sK3)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f42,f51,f24])).

fof(f51,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,sK3))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f32,f42,f19])).

fof(f354,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK1)
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f175,f336])).

fof(f175,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f54,f147,f23])).

fof(f147,plain,
    ( sK3 != k2_zfmisc_1(sK0,sK1)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f17,f132])).

fof(f54,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f42,f30])).

fof(f213,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl8_4
  <=> ! [X2] : ~ r2_hidden(X2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f287,plain,
    ( ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f210,f261,f30])).

fof(f261,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f249,f241])).

fof(f241,plain,
    ( ! [X0] : sK0 = k2_zfmisc_1(sK0,X0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f84,f228])).

fof(f228,plain,
    ( sK0 = sK3
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f42,f210,f24])).

fof(f84,plain,
    ( ! [X0] : sK3 = k2_zfmisc_1(sK3,X0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f42,f49,f24])).

fof(f49,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(sK3,X1))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f32,f42,f18])).

fof(f249,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f175,f228])).

fof(f210,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl8_3
  <=> ! [X3] : ~ r2_hidden(X3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f214,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f207,f41,f212,f209])).

fof(f207,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f121,f28])).

fof(f121,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f16])).

fof(f43,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f35,f41,f38])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f34,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (20400)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (20388)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (20391)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (20416)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (20389)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (20399)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (20408)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (20405)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (20395)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (20398)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (20392)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (20390)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (20409)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (20397)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (20401)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (20411)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (20387)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (20414)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (20413)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (20403)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (20413)Refutation not found, incomplete strategy% (20413)------------------------------
% 0.21/0.53  % (20413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20410)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (20393)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (20396)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (20412)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (20406)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (20404)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (20407)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (20402)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (20394)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (20391)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (20415)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (20413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20413)Memory used [KB]: 10746
% 0.21/0.55  % (20413)Time elapsed: 0.140 s
% 0.21/0.55  % (20413)------------------------------
% 0.21/0.55  % (20413)------------------------------
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1337,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f43,f214,f287,f387,f547,f563,f579,f635,f770,f830,f918,f1024,f1293])).
% 0.21/0.57  fof(f1293,plain,(
% 0.21/0.57    ~spl8_5 | spl8_7),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1284])).
% 0.21/0.57  fof(f1284,plain,(
% 0.21/0.57    $false | (~spl8_5 | spl8_7)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f1218,f624,f1130,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.57  fof(f1130,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,sK1))) ) | (~spl8_5 | spl8_7)),
% 0.21/0.57    inference(backward_demodulation,[],[f1074,f1113])).
% 0.21/0.57  fof(f1113,plain,(
% 0.21/0.57    sK1 = sK2 | (~spl8_5 | spl8_7)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f533,f624,f24])).
% 0.21/0.57  fof(f533,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl8_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f532])).
% 0.21/0.57  fof(f532,plain,(
% 0.21/0.57    spl8_5 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.57  fof(f1074,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,sK2))) ) | ~spl8_5),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f32,f533,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X1,X2,X3),X2) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f624,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl8_7),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f549,f558,f115])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X3,sK1) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f16,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) != k2_zfmisc_1(X0,X1) & ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))) => k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))) => k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_zfmisc_1)).
% 0.21/0.57  fof(f558,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK7(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl8_7),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f550,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f550,plain,(
% 0.21/0.57    ~r2_hidden(sK7(sK0,sK2),sK2) | spl8_7),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f546,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.57  fof(f546,plain,(
% 0.21/0.57    ~r1_tarski(sK0,sK2) | spl8_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f544])).
% 0.21/0.57  fof(f544,plain,(
% 0.21/0.57    spl8_7 <=> r1_tarski(sK0,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.57  fof(f549,plain,(
% 0.21/0.57    r2_hidden(sK7(sK0,sK2),sK0) | spl8_7),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f546,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f1218,plain,(
% 0.21/0.57    sK1 != k2_zfmisc_1(sK0,sK1) | (~spl8_5 | spl8_7)),
% 0.21/0.57    inference(backward_demodulation,[],[f1122,f1210])).
% 0.21/0.57  fof(f1210,plain,(
% 0.21/0.57    ( ! [X0] : (sK1 = k2_zfmisc_1(sK1,X0)) ) | (~spl8_5 | spl8_7)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f624,f1129,f24])).
% 0.21/0.57  fof(f1129,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK1,X1))) ) | (~spl8_5 | spl8_7)),
% 0.21/0.57    inference(backward_demodulation,[],[f1072,f1113])).
% 0.21/0.57  fof(f1072,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK2,X1))) ) | ~spl8_5),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f32,f533,f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3),X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f1122,plain,(
% 0.21/0.57    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK1,sK3) | (~spl8_5 | spl8_7)),
% 0.21/0.57    inference(backward_demodulation,[],[f17,f1113])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f1024,plain,(
% 0.21/0.57    ~spl8_5 | ~spl8_6),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1016])).
% 0.21/0.57  fof(f1016,plain,(
% 0.21/0.57    $false | (~spl8_5 | ~spl8_6)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f833,f972,f972,f24])).
% 0.21/0.57  fof(f972,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK0,X1))) ) | (~spl8_5 | ~spl8_6)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f32,f962,f18])).
% 0.21/0.57  fof(f962,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | (~spl8_5 | ~spl8_6)),
% 0.21/0.57    inference(forward_demodulation,[],[f533,f542])).
% 0.21/0.57  fof(f542,plain,(
% 0.21/0.57    sK0 = sK2 | ~spl8_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f540])).
% 0.21/0.57  fof(f540,plain,(
% 0.21/0.57    spl8_6 <=> sK0 = sK2),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.57  fof(f833,plain,(
% 0.21/0.57    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK3) | ~spl8_6),
% 0.21/0.57    inference(forward_demodulation,[],[f17,f542])).
% 0.21/0.57  fof(f918,plain,(
% 0.21/0.57    ~spl8_6 | spl8_10),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f910])).
% 0.21/0.57  fof(f910,plain,(
% 0.21/0.57    $false | (~spl8_6 | spl8_10)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f833,f847,f847,f24])).
% 0.21/0.57  fof(f847,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK0,X1))) ) | spl8_10),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f32,f627,f18])).
% 0.21/0.57  fof(f627,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl8_10),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f580,f595,f115])).
% 0.21/0.57  fof(f595,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK7(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl8_10),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f581,f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f581,plain,(
% 0.21/0.57    ~r2_hidden(sK7(sK1,sK3),sK3) | spl8_10),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f578,f31])).
% 0.21/0.57  fof(f578,plain,(
% 0.21/0.57    ~r1_tarski(sK1,sK3) | spl8_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f576])).
% 0.21/0.57  fof(f576,plain,(
% 0.21/0.57    spl8_10 <=> r1_tarski(sK1,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.57  fof(f580,plain,(
% 0.21/0.57    r2_hidden(sK7(sK1,sK3),sK1) | spl8_10),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f578,f30])).
% 0.21/0.57  fof(f830,plain,(
% 0.21/0.57    ~spl8_6 | ~spl8_9),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f829])).
% 0.21/0.57  fof(f829,plain,(
% 0.21/0.57    $false | (~spl8_6 | ~spl8_9)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f826])).
% 0.21/0.57  fof(f826,plain,(
% 0.21/0.57    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1) | (~spl8_6 | ~spl8_9)),
% 0.21/0.57    inference(backward_demodulation,[],[f638,f542])).
% 0.21/0.57  fof(f638,plain,(
% 0.21/0.57    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK1) | ~spl8_9),
% 0.21/0.57    inference(backward_demodulation,[],[f17,f574])).
% 0.21/0.57  fof(f574,plain,(
% 0.21/0.57    sK1 = sK3 | ~spl8_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f572])).
% 0.21/0.57  fof(f572,plain,(
% 0.21/0.57    spl8_9 <=> sK1 = sK3),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.57  fof(f770,plain,(
% 0.21/0.57    spl8_7 | ~spl8_9),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f762])).
% 0.21/0.57  fof(f762,plain,(
% 0.21/0.57    $false | (spl8_7 | ~spl8_9)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f638,f656,f656,f24])).
% 0.21/0.57  fof(f656,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,sK1))) ) | spl8_7),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f32,f624,f19])).
% 0.21/0.57  fof(f635,plain,(
% 0.21/0.57    spl8_7 | spl8_10),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f628])).
% 0.21/0.57  fof(f628,plain,(
% 0.21/0.57    $false | (spl8_7 | spl8_10)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f549,f580,f595,f115])).
% 0.21/0.57  fof(f579,plain,(
% 0.21/0.57    spl8_9 | ~spl8_10 | ~spl8_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f570,f561,f576,f572])).
% 0.21/0.57  fof(f561,plain,(
% 0.21/0.57    spl8_8 <=> ! [X2] : (~r2_hidden(X2,sK3) | r2_hidden(X2,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.57  fof(f570,plain,(
% 0.21/0.57    ~r1_tarski(sK1,sK3) | sK1 = sK3 | ~spl8_8),
% 0.21/0.57    inference(resolution,[],[f568,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f568,plain,(
% 0.21/0.57    r1_tarski(sK3,sK1) | ~spl8_8),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f567])).
% 0.21/0.57  fof(f567,plain,(
% 0.21/0.57    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl8_8),
% 0.21/0.57    inference(resolution,[],[f565,f30])).
% 0.21/0.57  fof(f565,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(sK7(X1,sK1),sK3) | r1_tarski(X1,sK1)) ) | ~spl8_8),
% 0.21/0.57    inference(resolution,[],[f562,f31])).
% 0.21/0.57  fof(f562,plain,(
% 0.21/0.57    ( ! [X2] : (r2_hidden(X2,sK1) | ~r2_hidden(X2,sK3)) ) | ~spl8_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f561])).
% 0.21/0.57  fof(f563,plain,(
% 0.21/0.57    spl8_5 | spl8_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f36,f561,f532])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(X2,sK3) | ~r2_hidden(X3,sK2) | r2_hidden(X2,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f34,f27])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK3) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.57    inference(resolution,[],[f15,f28])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f547,plain,(
% 0.21/0.57    spl8_6 | ~spl8_7 | ~spl8_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f538,f38,f544,f540])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    spl8_1 <=> ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.57  fof(f538,plain,(
% 0.21/0.57    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl8_1),
% 0.21/0.57    inference(resolution,[],[f536,f23])).
% 0.21/0.57  fof(f536,plain,(
% 0.21/0.57    r1_tarski(sK2,sK0) | ~spl8_1),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f535])).
% 0.21/0.57  fof(f535,plain,(
% 0.21/0.57    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0) | ~spl8_1),
% 0.21/0.57    inference(resolution,[],[f516,f30])).
% 0.21/0.57  fof(f516,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(sK7(X1,sK0),sK2) | r1_tarski(X1,sK0)) ) | ~spl8_1),
% 0.21/0.57    inference(resolution,[],[f39,f31])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X1] : (r2_hidden(X1,sK0) | ~r2_hidden(X1,sK2)) ) | ~spl8_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f38])).
% 0.21/0.57  fof(f387,plain,(
% 0.21/0.57    ~spl8_2 | ~spl8_4),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f380])).
% 0.21/0.57  fof(f380,plain,(
% 0.21/0.57    $false | (~spl8_2 | ~spl8_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f213,f365,f30])).
% 0.21/0.57  fof(f365,plain,(
% 0.21/0.57    ~r1_tarski(sK1,sK1) | (~spl8_2 | ~spl8_4)),
% 0.21/0.57    inference(forward_demodulation,[],[f354,f349])).
% 0.21/0.57  fof(f349,plain,(
% 0.21/0.57    ( ! [X0] : (sK1 = k2_zfmisc_1(X0,sK1)) ) | (~spl8_2 | ~spl8_4)),
% 0.21/0.57    inference(backward_demodulation,[],[f132,f336])).
% 0.21/0.57  fof(f336,plain,(
% 0.21/0.57    sK1 = sK3 | (~spl8_2 | ~spl8_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f42,f213,f24])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl8_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    spl8_2 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    ( ! [X0] : (sK3 = k2_zfmisc_1(X0,sK3)) ) | ~spl8_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f42,f51,f24])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,sK3))) ) | ~spl8_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f32,f42,f19])).
% 0.21/0.57  fof(f354,plain,(
% 0.21/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK1) | (~spl8_2 | ~spl8_4)),
% 0.21/0.57    inference(backward_demodulation,[],[f175,f336])).
% 0.21/0.57  fof(f175,plain,(
% 0.21/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | ~spl8_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f54,f147,f23])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    sK3 != k2_zfmisc_1(sK0,sK1) | ~spl8_2),
% 0.21/0.57    inference(backward_demodulation,[],[f17,f132])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl8_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f42,f30])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl8_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f212])).
% 0.21/0.57  fof(f212,plain,(
% 0.21/0.57    spl8_4 <=> ! [X2] : ~r2_hidden(X2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.57  fof(f287,plain,(
% 0.21/0.57    ~spl8_2 | ~spl8_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f280])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    $false | (~spl8_2 | ~spl8_3)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f210,f261,f30])).
% 0.21/0.57  fof(f261,plain,(
% 0.21/0.57    ~r1_tarski(sK0,sK0) | (~spl8_2 | ~spl8_3)),
% 0.21/0.57    inference(forward_demodulation,[],[f249,f241])).
% 0.21/0.57  fof(f241,plain,(
% 0.21/0.57    ( ! [X0] : (sK0 = k2_zfmisc_1(sK0,X0)) ) | (~spl8_2 | ~spl8_3)),
% 0.21/0.57    inference(backward_demodulation,[],[f84,f228])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    sK0 = sK3 | (~spl8_2 | ~spl8_3)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f42,f210,f24])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X0] : (sK3 = k2_zfmisc_1(sK3,X0)) ) | ~spl8_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f42,f49,f24])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK3,X1))) ) | ~spl8_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f32,f42,f18])).
% 0.21/0.57  fof(f249,plain,(
% 0.21/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK0) | (~spl8_2 | ~spl8_3)),
% 0.21/0.57    inference(backward_demodulation,[],[f175,f228])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    ( ! [X3] : (~r2_hidden(X3,sK0)) ) | ~spl8_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f209])).
% 0.21/0.57  fof(f209,plain,(
% 0.21/0.57    spl8_3 <=> ! [X3] : ~r2_hidden(X3,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.57  fof(f214,plain,(
% 0.21/0.57    spl8_3 | spl8_4 | ~spl8_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f207,f41,f212,f209])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(X2,sK1) | ~r2_hidden(X3,sK0)) ) | ~spl8_2),
% 0.21/0.57    inference(resolution,[],[f121,f28])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))) ) | ~spl8_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f51,f16])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    spl8_1 | spl8_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f35,f41,f38])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK2) | r2_hidden(X1,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f34,f26])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (20391)------------------------------
% 0.21/0.57  % (20391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20391)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (20391)Memory used [KB]: 6524
% 0.21/0.57  % (20391)Time elapsed: 0.148 s
% 0.21/0.57  % (20391)------------------------------
% 0.21/0.57  % (20391)------------------------------
% 0.21/0.57  % (20386)Success in time 0.214 s
%------------------------------------------------------------------------------
