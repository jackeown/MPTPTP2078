%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t151_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 6.57s
% Output     : Refutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 124 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 290 expanded)
%              Number of equality atoms :   14 (  35 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3389,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f893,f888,f885,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t151_funct_1.p',d4_xboole_0)).

fof(f885,plain,(
    ~ r2_hidden(sK9(sK2,sK1,sK3(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0))))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    inference(unit_resulting_resolution,[],[f100,f209,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k10_relat_1(sK2,X2))
      | ~ r2_hidden(sK9(sK2,X1,X0),X2)
      | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f98,f96])).

fof(f96,plain,(
    ! [X23,X21,X22] :
      ( ~ r2_hidden(k4_tarski(X21,X22),sK2)
      | ~ r2_hidden(X22,X23)
      | r2_hidden(X21,k10_relat_1(sK2,X23)) ) ),
    inference(resolution,[],[f42,f83])).

fof(f83,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t151_funct_1.p',d14_relat_1)).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t151_funct_1.p',t151_funct_1)).

fof(f98,plain,(
    ! [X26,X27] :
      ( r2_hidden(k4_tarski(X26,sK9(sK2,X27,X26)),sK2)
      | ~ r2_hidden(X26,k10_relat_1(sK2,X27)) ) ),
    inference(resolution,[],[f42,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK9(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK9(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f209,plain,(
    r2_hidden(sK3(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f99,plain,(
    r2_hidden(sK3(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t151_funct_1.p',d3_tarski)).

fof(f86,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))) ),
    inference(forward_demodulation,[],[f43,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t151_funct_1.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ~ r2_hidden(sK3(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))) ),
    inference(unit_resulting_resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f888,plain,(
    r2_hidden(sK9(sK2,sK1,sK3(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0))))),k9_relat_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f208,f209,f116])).

fof(f116,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK9(sK2,X4,X3),k9_relat_1(sK2,X5))
      | ~ r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k10_relat_1(sK2,X4)) ) ),
    inference(resolution,[],[f98,f93])).

fof(f93,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(k4_tarski(X14,X15),sK2)
      | ~ r2_hidden(X14,X16)
      | r2_hidden(X15,k9_relat_1(sK2,X16)) ) ),
    inference(resolution,[],[f42,f77])).

fof(f77,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t151_funct_1.p',d13_relat_1)).

fof(f208,plain,(
    r2_hidden(sK3(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),sK0) ),
    inference(unit_resulting_resolution,[],[f99,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f893,plain,(
    r2_hidden(sK9(sK2,sK1,sK3(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK1,k9_relat_1(sK2,sK0))))),sK1) ),
    inference(unit_resulting_resolution,[],[f42,f209,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
