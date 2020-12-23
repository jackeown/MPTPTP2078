%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t28_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 6.63s
% Output     : Refutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   31 (  63 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 131 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2280,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f160,f93,f131,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t28_relat_1.p',d5_xboole_0)).

fof(f131,plain,(
    r2_hidden(k4_tarski(sK4(sK0,sK2(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1)))),sK2(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1)))),sK0) ),
    inference(unit_resulting_resolution,[],[f113,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t28_relat_1.p',d5_relat_1)).

fof(f113,plain,(
    r2_hidden(sK2(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    r2_hidden(sK2(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t28_relat_1.p',d3_tarski)).

fof(f70,plain,(
    ~ r1_tarski(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f40,f47,f47])).

fof(f47,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t28_relat_1.p',redefinition_k6_subset_1)).

fof(f40,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t28_relat_1.p',t28_relat_1)).

fof(f93,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1)))),k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f78,f73])).

fof(f73,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X3,X2),X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ~ r2_hidden(sK2(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))),k2_relat_1(k4_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1)))),sK1) ),
    inference(unit_resulting_resolution,[],[f114,f73])).

fof(f114,plain,(
    ~ r2_hidden(sK2(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
