%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t183_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:56 EDT 2019

% Result     : Theorem 6.75s
% Output     : Refutation 6.75s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 117 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 263 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5468,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f164,f5465])).

fof(f5465,plain,(
    ~ spl13_0 ),
    inference(avatar_contradiction_clause,[],[f5443])).

fof(f5443,plain,
    ( $false
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f749,f110,f750,f807])).

fof(f807,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,k10_relat_1(k4_relat_1(sK1),X1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X2),sK1) )
    | ~ spl13_0 ),
    inference(resolution,[],[f123,f153])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl13_0
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f123,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(k4_tarski(X13,X14),k4_relat_1(sK1))
      | ~ r2_hidden(X14,X15)
      | r2_hidden(X13,k10_relat_1(k4_relat_1(sK1),X15)) ) ),
    inference(resolution,[],[f98,f86])).

fof(f86,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t183_relat_1.p',d14_relat_1)).

fof(f98,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t183_relat_1.p',dt_k4_relat_1)).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t183_relat_1.p',t183_relat_1)).

fof(f750,plain,(
    r2_hidden(k4_tarski(sK10(sK1,sK2(k3_xboole_0(sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),sK2(k3_xboole_0(sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),sK1) ),
    inference(unit_resulting_resolution,[],[f167,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK10(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t183_relat_1.p',d5_relat_1)).

fof(f167,plain,(
    r2_hidden(sK2(k3_xboole_0(sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f109,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t183_relat_1.p',d4_xboole_0)).

fof(f109,plain,(
    r2_hidden(sK2(k3_xboole_0(sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k3_xboole_0(sK0,k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f96,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t183_relat_1.p',d3_tarski)).

fof(f96,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f48,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t183_relat_1.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f110,plain,(
    ~ r2_hidden(sK2(k3_xboole_0(sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f96,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f749,plain,(
    r2_hidden(sK10(sK1,sK2(k3_xboole_0(sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),k10_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f166,f167,f142])).

fof(f142,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK10(sK1,X2),k10_relat_1(sK1,X3))
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f106,f94])).

fof(f106,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X10),sK1)
      | ~ r2_hidden(X10,X11)
      | r2_hidden(X9,k10_relat_1(sK1,X11)) ) ),
    inference(resolution,[],[f47,f86])).

fof(f166,plain,(
    r2_hidden(sK2(k3_xboole_0(sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f109,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f164,plain,(
    spl13_3 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl13_3 ),
    inference(unit_resulting_resolution,[],[f47,f159])).

fof(f159,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl13_3
  <=> ~ v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f160,plain,
    ( spl13_0
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f114,f158,f152])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK1)) ) ),
    inference(resolution,[],[f98,f90])).

fof(f90,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k4_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t183_relat_1.p',d7_relat_1)).
%------------------------------------------------------------------------------
