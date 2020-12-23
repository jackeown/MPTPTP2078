%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0773+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 115 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 301 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(subsumption_resolution,[],[f225,f151])).

fof(f151,plain,(
    ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f150,f16])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ v1_relat_2(k2_wellord1(X1,X0))
      & v1_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ v1_relat_2(k2_wellord1(X1,X0))
      & v1_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v1_relat_2(X1)
         => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
       => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_wellord1)).

fof(f150,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f48,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f48,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    inference(resolution,[],[f18,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(f18,plain,(
    ~ v1_relat_2(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f225,plain,(
    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    inference(resolution,[],[f221,f117])).

fof(f117,plain,(
    r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f115,f44])).

fof(f44,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k3_relat_1(k2_wellord1(sK1,X6)))
      | r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f16,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f115,plain,(
    r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(k2_wellord1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f114,f16])).

fof(f114,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(k2_wellord1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f47,f23])).

fof(f47,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(k2_wellord1(sK1,sK0))) ),
    inference(resolution,[],[f18,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0),k3_relat_1(X0))
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f221,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X2)
      | r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X2))
      | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X2)
      | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X2) ) ),
    inference(resolution,[],[f144,f129])).

fof(f129,plain,(
    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1) ),
    inference(resolution,[],[f116,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f45,f16])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k3_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,X0),sK1) ) ),
    inference(resolution,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    v1_relat_2(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f116,plain,(
    r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k3_relat_1(k2_wellord1(sK1,X4)))
      | r2_hidden(X3,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f16,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f144,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(k4_tarski(X17,X18),sK1)
      | r2_hidden(k4_tarski(X17,X18),k2_wellord1(sK1,X19))
      | ~ r2_hidden(X17,X19)
      | ~ r2_hidden(X18,X19) ) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f57,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X12,k2_zfmisc_1(X11,X11))
      | ~ r2_hidden(X12,sK1)
      | r2_hidden(X12,k2_wellord1(sK1,X11)) ) ),
    inference(superposition,[],[f35,f41])).

fof(f41,plain,(
    ! [X1] : k2_wellord1(sK1,X1) = k3_xboole_0(sK1,k2_zfmisc_1(X1,X1)) ),
    inference(resolution,[],[f16,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

%------------------------------------------------------------------------------
