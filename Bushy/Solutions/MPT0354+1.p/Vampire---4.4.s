%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t33_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:22 EDT 2019

% Result     : Theorem 10.49s
% Output     : Refutation 10.49s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 135 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 261 expanded)
%              Number of equality atoms :   49 (  98 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75940,plain,(
    $false ),
    inference(subsumption_resolution,[],[f75811,f513])).

fof(f513,plain,(
    k3_subset_1(sK0,k6_subset_1(sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f502,f70])).

fof(f70,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t33_subset_1)).

fof(f502,plain,(
    ! [X5] : k7_subset_1(sK0,sK1,X5) = k6_subset_1(sK1,X5) ),
    inference(resolution,[],[f116,f71])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f105,f84])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',redefinition_k6_subset_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',redefinition_k7_subset_1)).

fof(f75811,plain,(
    k3_subset_1(sK0,k6_subset_1(sK1,sK2)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f75786,f3797])).

fof(f3797,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3772,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',commutativity_k2_xboole_0)).

fof(f3772,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) = k2_xboole_0(k3_subset_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f1700,f373])).

fof(f373,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f82,f341])).

fof(f341,plain,(
    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f114,f71])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f94,f84])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',d5_subset_1)).

fof(f82,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',dt_k6_subset_1)).

fof(f1700,plain,(
    ! [X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X18,sK2) = k2_xboole_0(X18,sK2) ) ),
    inference(resolution,[],[f110,f69])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',redefinition_k4_subset_1)).

fof(f75786,plain,(
    k3_subset_1(sK0,k6_subset_1(sK1,sK2)) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f9762,f206])).

fof(f206,plain,(
    k3_xboole_0(sK0,sK2) = sK2 ),
    inference(superposition,[],[f201,f85])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',commutativity_k3_xboole_0)).

fof(f201,plain,(
    k3_xboole_0(sK2,sK0) = sK2 ),
    inference(resolution,[],[f90,f160])).

fof(f160,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f159,f69])).

fof(f159,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | r1_tarski(X7,X6) ) ),
    inference(subsumption_resolution,[],[f157,f73])).

fof(f73,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',fc1_subset_1)).

fof(f157,plain,(
    ! [X6,X7] :
      ( v1_xboole_0(k1_zfmisc_1(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | r1_tarski(X7,X6) ) ),
    inference(resolution,[],[f89,f117])).

fof(f117,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',d1_zfmisc_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',d2_subset_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t28_xboole_1)).

fof(f9762,plain,(
    ! [X38] : k3_subset_1(sK0,k6_subset_1(sK1,X38)) = k2_xboole_0(k3_xboole_0(sK0,X38),k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f9663,f699])).

fof(f699,plain,(
    ! [X4] : k3_subset_1(sK0,k6_subset_1(sK1,X4)) = k6_subset_1(sK0,k6_subset_1(sK1,X4)) ),
    inference(resolution,[],[f658,f114])).

fof(f658,plain,(
    ! [X2] : m1_subset_1(k6_subset_1(sK1,X2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f625,f204])).

fof(f204,plain,(
    ! [X2,X1] : k3_xboole_0(k6_subset_1(X1,X2),X1) = k6_subset_1(X1,X2) ),
    inference(resolution,[],[f90,f162])).

fof(f162,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[],[f159,f82])).

fof(f625,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f623,f71])).

fof(f623,plain,(
    ! [X1] :
      ( m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f104,f396])).

fof(f396,plain,(
    ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(sK0,X1,sK1) ),
    inference(resolution,[],[f106,f71])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',redefinition_k9_subset_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',dt_k9_subset_1)).

fof(f9663,plain,(
    ! [X38] : k2_xboole_0(k3_xboole_0(sK0,X38),k3_subset_1(sK0,sK1)) = k6_subset_1(sK0,k6_subset_1(sK1,X38)) ),
    inference(superposition,[],[f885,f341])).

fof(f885,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k3_xboole_0(X3,X5),k6_subset_1(X3,X4)) = k6_subset_1(X3,k6_subset_1(X4,X5)) ),
    inference(superposition,[],[f115,f83])).

fof(f115,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k6_subset_1(X0,X1),k3_xboole_0(X0,X2)) = k6_subset_1(X0,k6_subset_1(X1,X2)) ),
    inference(definition_unfolding,[],[f101,f84,f84,f84])).

fof(f101,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t52_xboole_1)).
%------------------------------------------------------------------------------
