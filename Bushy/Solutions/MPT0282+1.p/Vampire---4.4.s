%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t83_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:12 EDT 2019

% Result     : Theorem 6.63s
% Output     : Refutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 112 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 260 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f277,f329,f369])).

fof(f369,plain,
    ( ~ spl5_0
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f43,f345,f319,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',t1_xboole_1)).

fof(f319,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f157,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',d1_zfmisc_1)).

fof(f157,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl5_4
  <=> r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f345,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f332,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f332,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f157,f151,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',d4_xboole_0)).

fof(f151,plain,
    ( ! [X1] : ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(sK0),X1))
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_0
  <=> ! [X1] : ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(sK0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',t17_xboole_1)).

fof(f329,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f306,f157,f56])).

fof(f306,plain,
    ( ! [X0] : ~ r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(X0,sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f296,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(f296,plain,
    ( ! [X0] : ~ r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,X0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f43,f289,f50])).

fof(f289,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f287,f57])).

fof(f287,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f154,f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',idempotence_k3_xboole_0)).

fof(f154,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(sK1),X0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_2
  <=> ! [X0] : ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f277,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f173,f218,f164,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',t19_xboole_1)).

fof(f164,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f160,f57])).

fof(f160,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl5_5
  <=> ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f218,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f163,f56])).

fof(f163,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f31,f160,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) != k1_zfmisc_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) != k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',t83_zfmisc_1)).

fof(f173,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f162,f56])).

fof(f162,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f31,f160,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f161,plain,
    ( spl5_0
    | spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f97,f159,f153,f150])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(sK1),X0))
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(sK0),X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X5] :
      ( k1_zfmisc_1(k3_xboole_0(sK0,sK1)) != X4
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X4),X4)
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X4),k3_xboole_0(k1_zfmisc_1(sK1),X5))
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X4),k3_xboole_0(k1_zfmisc_1(sK0),X6)) ) ),
    inference(resolution,[],[f62,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X1),k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X1),X1)
      | k1_zfmisc_1(k3_xboole_0(sK0,sK1)) != X1
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X1),k3_xboole_0(k1_zfmisc_1(sK1),X2)) ) ),
    inference(resolution,[],[f58,f55])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X0),k1_zfmisc_1(sK1))
      | k1_zfmisc_1(k3_xboole_0(sK0,sK1)) != X0
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X0),X0)
      | ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X0),k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f31,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
