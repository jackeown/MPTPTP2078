%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t146_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 6.63s
% Output     : Refutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   32 (  84 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 228 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1246,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f98,f115,f747,f317])).

fof(f317,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK10(sK1,X5),k9_relat_1(sK1,X6))
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X5,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f88,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK10(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK10(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t146_funct_1.p',d4_relat_1)).

fof(f88,plain,(
    ! [X23,X21,X22] :
      ( ~ r2_hidden(k4_tarski(X21,X22),sK1)
      | ~ r2_hidden(X21,X23)
      | r2_hidden(X22,k9_relat_1(sK1,X23)) ) ),
    inference(resolution,[],[f39,f74])).

fof(f74,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t146_funct_1.p',d13_relat_1)).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t146_funct_1.p',t146_funct_1)).

fof(f747,plain,(
    ~ r2_hidden(sK10(sK1,sK8(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),k9_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f115,f99,f170])).

fof(f170,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK10(sK1,X2),X3)
      | r2_hidden(X2,k10_relat_1(sK1,X3))
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f85,f77])).

fof(f85,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(k4_tarski(X14,X15),sK1)
      | ~ r2_hidden(X15,X16)
      | r2_hidden(X14,k10_relat_1(sK1,X16)) ) ),
    inference(resolution,[],[f39,f71])).

fof(f71,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t146_funct_1.p',d14_relat_1)).

fof(f99,plain,(
    ~ r2_hidden(sK8(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t146_funct_1.p',d3_tarski)).

fof(f41,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f115,plain,(
    r2_hidden(sK8(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f98,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    r2_hidden(sK8(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
