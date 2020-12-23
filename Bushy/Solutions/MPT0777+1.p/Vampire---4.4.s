%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t26_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  42 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  67 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4146,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f4144])).

fof(f4144,plain,(
    k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f16,f4141])).

fof(f4141,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f4139,f119])).

fof(f119,plain,(
    ! [X2,X3] : k2_wellord1(sK2,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_wellord1(sK2,X2),k2_zfmisc_1(X3,X3)) ),
    inference(superposition,[],[f62,f28])).

fof(f28,plain,(
    ! [X8,X9] : k3_xboole_0(k2_wellord1(sK2,X8),X9) = k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X8,X8),X9)) ),
    inference(superposition,[],[f21,f23])).

fof(f23,plain,(
    ! [X0] : k2_wellord1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f17,f15])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t26_wellord1.p',t26_wellord1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t26_wellord1.p',d6_wellord1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t26_wellord1.p',t16_xboole_1)).

fof(f62,plain,(
    ! [X6,X5] : k2_wellord1(sK2,k3_xboole_0(X5,X6)) = k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X5,X5),k2_zfmisc_1(X6,X6))) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t26_wellord1.p',t123_zfmisc_1)).

fof(f4139,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)) ),
    inference(resolution,[],[f24,f15])).

fof(f24,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(k2_wellord1(X1,X2),X3) = k3_xboole_0(k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3)) ) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t26_wellord1.p',dt_k2_wellord1)).

fof(f16,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
