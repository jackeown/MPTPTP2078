%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t97_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:13 EDT 2019

% Result     : Theorem 6.69s
% Output     : Refutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :   31 (  76 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 161 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f369,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f252,f53,f253,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t97_zfmisc_1.p',d4_xboole_0)).

fof(f253,plain,(
    r2_hidden(sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f86,f55,f46])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t97_zfmisc_1.p',d4_tarski)).

fof(f55,plain,(
    r2_hidden(sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK4(k3_xboole_0(sK0,sK1),sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))) ),
    inference(unit_resulting_resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_tarski(X0))
      | r2_hidden(X2,sK4(X0,X2)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK4(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    r2_hidden(sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(k3_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t97_zfmisc_1.p',d3_tarski)).

fof(f24,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t97_zfmisc_1.p',t97_zfmisc_1)).

fof(f86,plain,(
    r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK1) ),
    inference(unit_resulting_resolution,[],[f56,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f52,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_tarski(X0))
      | r2_hidden(sK4(X0,X2),X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ~ r2_hidden(sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f252,plain,(
    r2_hidden(sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f85,f55,f46])).

fof(f85,plain,(
    r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK0) ),
    inference(unit_resulting_resolution,[],[f56,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
