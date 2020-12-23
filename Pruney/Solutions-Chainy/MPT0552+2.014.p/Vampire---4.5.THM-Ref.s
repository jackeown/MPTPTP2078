%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:46 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 479 expanded)
%              Number of leaves         :   14 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :  224 ( 901 expanded)
%              Number of equality atoms :   34 ( 288 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f772,plain,(
    $false ),
    inference(resolution,[],[f633,f716])).

fof(f716,plain,(
    ! [X101,X100] : r1_tarski(k9_relat_1(k7_relat_1(sK2,X100),X101),k9_relat_1(sK2,X100)) ),
    inference(forward_demodulation,[],[f678,f581])).

fof(f581,plain,(
    ! [X8] : k9_relat_1(k7_relat_1(sK2,X8),X8) = k9_relat_1(sK2,X8) ),
    inference(superposition,[],[f147,f574])).

fof(f574,plain,(
    ! [X5] : k1_setfam_1(k1_enumset1(X5,X5,X5)) = X5 ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,(
    ! [X5] :
      ( k1_setfam_1(k1_enumset1(X5,X5,X5)) = X5
      | k1_setfam_1(k1_enumset1(X5,X5,X5)) = X5 ) ),
    inference(resolution,[],[f563,f352])).

fof(f352,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(factoring,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f563,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11 ) ),
    inference(subsumption_resolution,[],[f560,f61])).

fof(f560,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X11)
      | ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11 ) ),
    inference(duplicate_literal_removal,[],[f557])).

fof(f557,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X11)
      | ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11
      | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11 ) ),
    inference(resolution,[],[f63,f352])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f147,plain,(
    ! [X17,X18] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X17,X17,X18))) = k9_relat_1(k7_relat_1(sK2,X17),X18) ),
    inference(forward_demodulation,[],[f140,f109])).

fof(f109,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3) ) ),
    inference(resolution,[],[f41,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f140,plain,(
    ! [X17,X18] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X17,X17,X18))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X17),X18)) ),
    inference(superposition,[],[f78,f130])).

fof(f130,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(resolution,[],[f56,f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f78,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f41,f30])).

fof(f678,plain,(
    ! [X101,X100] : r1_tarski(k9_relat_1(k7_relat_1(sK2,X100),X101),k9_relat_1(k7_relat_1(sK2,X100),X100)) ),
    inference(superposition,[],[f236,f580])).

fof(f580,plain,(
    ! [X7] : k7_relat_1(sK2,X7) = k7_relat_1(k7_relat_1(sK2,X7),X7) ),
    inference(superposition,[],[f130,f574])).

fof(f236,plain,(
    ! [X2,X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2),k9_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(forward_demodulation,[],[f235,f138])).

fof(f138,plain,(
    ! [X12,X13,X11] : k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X11),X12),X13)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X11),X12),X13) ),
    inference(superposition,[],[f109,f130])).

fof(f235,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2)),k9_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(subsumption_resolution,[],[f232,f158])).

fof(f158,plain,(
    ! [X30,X29] : v1_relat_1(k7_relat_1(k7_relat_1(sK2,X29),X30)) ),
    inference(subsumption_resolution,[],[f145,f30])).

fof(f145,plain,(
    ! [X30,X29] :
      ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X29),X30))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f38,f130])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2)),k9_relat_1(k7_relat_1(sK2,X0),X1))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ) ),
    inference(resolution,[],[f210,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f210,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_tarski(X13,k7_relat_1(k7_relat_1(sK2,X11),X12))
      | r1_tarski(k2_relat_1(X13),k9_relat_1(k7_relat_1(sK2,X11),X12)) ) ),
    inference(forward_demodulation,[],[f200,f130])).

fof(f200,plain,(
    ! [X12,X13,X11] :
      ( r1_tarski(k2_relat_1(X13),k9_relat_1(k7_relat_1(sK2,X11),X12))
      | ~ r1_tarski(X13,k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X11,X11,X12)))) ) ),
    inference(superposition,[],[f92,f147])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1))
      | ~ r1_tarski(X0,k7_relat_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f91,f30])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1))
      | ~ r1_tarski(X0,k7_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f89,f38])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
      | r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0))
      | ~ r1_tarski(X1,k7_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f87,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0))
      | ~ r1_tarski(X1,k7_relat_1(sK2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f33,f78])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f633,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f576,f434])).

fof(f434,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f429,f152])).

fof(f152,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f148,f147])).

fof(f148,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f125,f147])).

fof(f125,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f54,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f54,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f31,f53,f53])).

fof(f31,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f429,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X2),X0),k9_relat_1(sK2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f428,f78])).

fof(f428,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X2),X0),k2_relat_1(k7_relat_1(sK2,X1))) ) ),
    inference(subsumption_resolution,[],[f427,f30])).

fof(f427,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X2),X0),k2_relat_1(k7_relat_1(sK2,X1))) ) ),
    inference(duplicate_literal_removal,[],[f422])).

fof(f422,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X2),X0),k2_relat_1(k7_relat_1(sK2,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f277,f39])).

fof(f277,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k7_relat_1(sK2,X1),X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k2_relat_1(k7_relat_1(X0,X3))) ) ),
    inference(subsumption_resolution,[],[f276,f38])).

fof(f276,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k7_relat_1(sK2,X1),X0)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(k7_relat_1(X0,X3))
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k2_relat_1(k7_relat_1(X0,X3))) ) ),
    inference(subsumption_resolution,[],[f266,f68])).

fof(f266,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k7_relat_1(sK2,X1),X0)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(k7_relat_1(sK2,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X3))
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k2_relat_1(k7_relat_1(X0,X3))) ) ),
    inference(resolution,[],[f45,f124])).

fof(f124,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,X11),X12),X13)
      | ~ v1_relat_1(X13)
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X11),X12),k2_relat_1(X13)) ) ),
    inference(subsumption_resolution,[],[f120,f68])).

fof(f120,plain,(
    ! [X12,X13,X11] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X11),X12),k2_relat_1(X13))
      | ~ v1_relat_1(X13)
      | ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,X11),X12),X13)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,X11),X12)) ) ),
    inference(superposition,[],[f33,f109])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f576,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f55,f574])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (14331)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (14323)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (14317)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (14310)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (14308)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (14312)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (14313)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (14320)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (14321)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (14333)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (14328)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (14337)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (14329)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (14334)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (14327)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (14325)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (14336)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (14319)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (14325)Refutation not found, incomplete strategy% (14325)------------------------------
% 0.21/0.55  % (14325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14311)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (14309)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (14314)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (14332)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (14325)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14325)Memory used [KB]: 10618
% 0.21/0.56  % (14325)Time elapsed: 0.150 s
% 0.21/0.56  % (14325)------------------------------
% 0.21/0.56  % (14325)------------------------------
% 0.21/0.57  % (14330)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (14330)Refutation not found, incomplete strategy% (14330)------------------------------
% 0.21/0.57  % (14330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14330)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14330)Memory used [KB]: 10746
% 0.21/0.57  % (14330)Time elapsed: 0.163 s
% 0.21/0.57  % (14330)------------------------------
% 0.21/0.57  % (14330)------------------------------
% 0.21/0.57  % (14335)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.58  % (14324)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (14315)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.58  % (14322)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (14316)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.67/0.60  % (14318)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.67/0.60  % (14318)Refutation not found, incomplete strategy% (14318)------------------------------
% 1.67/0.60  % (14318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (14318)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.60  
% 1.67/0.60  % (14318)Memory used [KB]: 10618
% 1.67/0.60  % (14318)Time elapsed: 0.175 s
% 1.67/0.60  % (14318)------------------------------
% 1.67/0.60  % (14318)------------------------------
% 1.67/0.60  % (14326)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.20/0.67  % (14314)Refutation found. Thanks to Tanya!
% 2.20/0.67  % SZS status Theorem for theBenchmark
% 2.20/0.67  % SZS output start Proof for theBenchmark
% 2.20/0.67  fof(f772,plain,(
% 2.20/0.67    $false),
% 2.20/0.67    inference(resolution,[],[f633,f716])).
% 2.20/0.67  fof(f716,plain,(
% 2.20/0.67    ( ! [X101,X100] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X100),X101),k9_relat_1(sK2,X100))) )),
% 2.20/0.67    inference(forward_demodulation,[],[f678,f581])).
% 2.20/0.67  fof(f581,plain,(
% 2.20/0.67    ( ! [X8] : (k9_relat_1(k7_relat_1(sK2,X8),X8) = k9_relat_1(sK2,X8)) )),
% 2.20/0.67    inference(superposition,[],[f147,f574])).
% 2.20/0.67  fof(f574,plain,(
% 2.20/0.67    ( ! [X5] : (k1_setfam_1(k1_enumset1(X5,X5,X5)) = X5) )),
% 2.20/0.67    inference(duplicate_literal_removal,[],[f571])).
% 2.20/0.67  fof(f571,plain,(
% 2.20/0.67    ( ! [X5] : (k1_setfam_1(k1_enumset1(X5,X5,X5)) = X5 | k1_setfam_1(k1_enumset1(X5,X5,X5)) = X5) )),
% 2.20/0.67    inference(resolution,[],[f563,f352])).
% 2.20/0.67  fof(f352,plain,(
% 2.20/0.67    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X1) )),
% 2.20/0.67    inference(factoring,[],[f61])).
% 2.20/0.67  fof(f61,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2) )),
% 2.20/0.67    inference(definition_unfolding,[],[f49,f53])).
% 2.20/0.67  fof(f53,plain,(
% 2.20/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.20/0.67    inference(definition_unfolding,[],[f36,f37])).
% 2.20/0.67  fof(f37,plain,(
% 2.20/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f4])).
% 2.20/0.67  fof(f4,axiom,(
% 2.20/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.20/0.67  fof(f36,plain,(
% 2.20/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.20/0.67    inference(cnf_transformation,[],[f5])).
% 2.20/0.67  fof(f5,axiom,(
% 2.20/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.20/0.67  fof(f49,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.20/0.67    inference(cnf_transformation,[],[f1])).
% 2.20/0.67  fof(f1,axiom,(
% 2.20/0.67    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.20/0.67  fof(f563,plain,(
% 2.20/0.67    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f560,f61])).
% 2.20/0.67  fof(f560,plain,(
% 2.20/0.67    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X11) | ~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11) )),
% 2.20/0.67    inference(duplicate_literal_removal,[],[f557])).
% 2.20/0.67  fof(f557,plain,(
% 2.20/0.67    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X11) | ~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11 | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11) )),
% 2.20/0.67    inference(resolution,[],[f63,f352])).
% 2.20/0.67  fof(f63,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2) )),
% 2.20/0.67    inference(definition_unfolding,[],[f47,f53])).
% 2.20/0.67  fof(f47,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.20/0.67    inference(cnf_transformation,[],[f1])).
% 2.20/0.67  fof(f147,plain,(
% 2.20/0.67    ( ! [X17,X18] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X17,X17,X18))) = k9_relat_1(k7_relat_1(sK2,X17),X18)) )),
% 2.20/0.67    inference(forward_demodulation,[],[f140,f109])).
% 2.20/0.67  fof(f109,plain,(
% 2.20/0.67    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 2.20/0.67    inference(resolution,[],[f79,f30])).
% 2.20/0.67  fof(f30,plain,(
% 2.20/0.67    v1_relat_1(sK2)),
% 2.20/0.67    inference(cnf_transformation,[],[f17])).
% 2.20/0.67  fof(f17,plain,(
% 2.20/0.67    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 2.20/0.67    inference(ennf_transformation,[],[f16])).
% 2.20/0.67  fof(f16,negated_conjecture,(
% 2.20/0.67    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.20/0.67    inference(negated_conjecture,[],[f15])).
% 2.20/0.67  fof(f15,conjecture,(
% 2.20/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 2.20/0.67  fof(f79,plain,(
% 2.20/0.67    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)) )),
% 2.20/0.67    inference(resolution,[],[f41,f38])).
% 2.20/0.67  fof(f38,plain,(
% 2.20/0.67    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f21])).
% 2.20/0.67  fof(f21,plain,(
% 2.20/0.67    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.20/0.67    inference(ennf_transformation,[],[f8])).
% 2.20/0.67  fof(f8,axiom,(
% 2.20/0.67    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.20/0.67  fof(f41,plain,(
% 2.20/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f24])).
% 2.20/0.67  fof(f24,plain,(
% 2.20/0.67    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.20/0.67    inference(ennf_transformation,[],[f11])).
% 2.20/0.67  fof(f11,axiom,(
% 2.20/0.67    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.20/0.67  fof(f140,plain,(
% 2.20/0.67    ( ! [X17,X18] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X17,X17,X18))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X17),X18))) )),
% 2.20/0.67    inference(superposition,[],[f78,f130])).
% 2.20/0.67  fof(f130,plain,(
% 2.20/0.67    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 2.20/0.67    inference(resolution,[],[f56,f30])).
% 2.20/0.67  fof(f56,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 2.20/0.67    inference(definition_unfolding,[],[f44,f53])).
% 2.20/0.67  fof(f44,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 2.20/0.67    inference(cnf_transformation,[],[f25])).
% 2.20/0.67  fof(f25,plain,(
% 2.20/0.67    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.20/0.67    inference(ennf_transformation,[],[f9])).
% 2.20/0.67  fof(f9,axiom,(
% 2.20/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 2.20/0.67  fof(f78,plain,(
% 2.20/0.67    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 2.20/0.67    inference(resolution,[],[f41,f30])).
% 2.20/0.67  fof(f678,plain,(
% 2.20/0.67    ( ! [X101,X100] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X100),X101),k9_relat_1(k7_relat_1(sK2,X100),X100))) )),
% 2.20/0.67    inference(superposition,[],[f236,f580])).
% 2.20/0.67  fof(f580,plain,(
% 2.20/0.67    ( ! [X7] : (k7_relat_1(sK2,X7) = k7_relat_1(k7_relat_1(sK2,X7),X7)) )),
% 2.20/0.67    inference(superposition,[],[f130,f574])).
% 2.20/0.67  fof(f236,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2),k9_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 2.20/0.67    inference(forward_demodulation,[],[f235,f138])).
% 2.20/0.67  fof(f138,plain,(
% 2.20/0.67    ( ! [X12,X13,X11] : (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X11),X12),X13)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X11),X12),X13)) )),
% 2.20/0.67    inference(superposition,[],[f109,f130])).
% 2.20/0.67  fof(f235,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2)),k9_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f232,f158])).
% 2.20/0.67  fof(f158,plain,(
% 2.20/0.67    ( ! [X30,X29] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X29),X30))) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f145,f30])).
% 2.20/0.67  fof(f145,plain,(
% 2.20/0.67    ( ! [X30,X29] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X29),X30)) | ~v1_relat_1(sK2)) )),
% 2.20/0.67    inference(superposition,[],[f38,f130])).
% 2.20/0.67  fof(f232,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2)),k9_relat_1(k7_relat_1(sK2,X0),X1)) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 2.20/0.67    inference(resolution,[],[f210,f39])).
% 2.20/0.67  fof(f39,plain,(
% 2.20/0.67    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f22])).
% 2.20/0.67  fof(f22,plain,(
% 2.20/0.67    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.20/0.67    inference(ennf_transformation,[],[f13])).
% 2.20/0.67  fof(f13,axiom,(
% 2.20/0.67    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 2.20/0.67  fof(f210,plain,(
% 2.20/0.67    ( ! [X12,X13,X11] : (~r1_tarski(X13,k7_relat_1(k7_relat_1(sK2,X11),X12)) | r1_tarski(k2_relat_1(X13),k9_relat_1(k7_relat_1(sK2,X11),X12))) )),
% 2.20/0.67    inference(forward_demodulation,[],[f200,f130])).
% 2.20/0.67  fof(f200,plain,(
% 2.20/0.67    ( ! [X12,X13,X11] : (r1_tarski(k2_relat_1(X13),k9_relat_1(k7_relat_1(sK2,X11),X12)) | ~r1_tarski(X13,k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X11,X11,X12))))) )),
% 2.20/0.67    inference(superposition,[],[f92,f147])).
% 2.20/0.67  fof(f92,plain,(
% 2.20/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,k7_relat_1(sK2,X1))) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f91,f30])).
% 2.20/0.67  fof(f91,plain,(
% 2.20/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,k7_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 2.20/0.67    inference(resolution,[],[f89,f38])).
% 2.20/0.67  fof(f89,plain,(
% 2.20/0.67    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK2,X0)) | r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0)) | ~r1_tarski(X1,k7_relat_1(sK2,X0))) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f87,f68])).
% 2.20/0.67  fof(f68,plain,(
% 2.20/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(X1) | ~r1_tarski(X1,X0)) )),
% 2.20/0.67    inference(resolution,[],[f34,f42])).
% 2.20/0.67  fof(f42,plain,(
% 2.20/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f6])).
% 2.20/0.67  fof(f6,axiom,(
% 2.20/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.20/0.67  fof(f34,plain,(
% 2.20/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f20])).
% 2.20/0.67  fof(f20,plain,(
% 2.20/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.20/0.67    inference(ennf_transformation,[],[f7])).
% 2.20/0.67  fof(f7,axiom,(
% 2.20/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.20/0.67  fof(f87,plain,(
% 2.20/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0)) | ~r1_tarski(X1,k7_relat_1(sK2,X0)) | ~v1_relat_1(X1)) )),
% 2.20/0.67    inference(superposition,[],[f33,f78])).
% 2.20/0.67  fof(f33,plain,(
% 2.20/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f19])).
% 2.20/0.67  fof(f19,plain,(
% 2.20/0.67    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.20/0.67    inference(flattening,[],[f18])).
% 2.20/0.67  fof(f18,plain,(
% 2.20/0.67    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.20/0.67    inference(ennf_transformation,[],[f12])).
% 2.20/0.67  fof(f12,axiom,(
% 2.20/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 2.20/0.67  fof(f633,plain,(
% 2.20/0.67    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0))),
% 2.20/0.67    inference(resolution,[],[f576,f434])).
% 2.20/0.67  fof(f434,plain,(
% 2.20/0.67    ~r1_tarski(sK1,sK1) | ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0))),
% 2.20/0.67    inference(resolution,[],[f429,f152])).
% 2.20/0.67  fof(f152,plain,(
% 2.20/0.67    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0))),
% 2.20/0.67    inference(forward_demodulation,[],[f148,f147])).
% 2.20/0.67  fof(f148,plain,(
% 2.20/0.67    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1))),
% 2.20/0.67    inference(backward_demodulation,[],[f125,f147])).
% 2.20/0.67  fof(f125,plain,(
% 2.20/0.67    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0))),
% 2.20/0.67    inference(resolution,[],[f54,f57])).
% 2.20/0.67  fof(f57,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.20/0.67    inference(definition_unfolding,[],[f46,f53])).
% 2.20/0.67  fof(f46,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 2.20/0.67    inference(cnf_transformation,[],[f29])).
% 2.20/0.67  fof(f29,plain,(
% 2.20/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.20/0.67    inference(flattening,[],[f28])).
% 2.20/0.67  fof(f28,plain,(
% 2.20/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.20/0.67    inference(ennf_transformation,[],[f3])).
% 2.20/0.67  fof(f3,axiom,(
% 2.20/0.67    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.20/0.67  fof(f54,plain,(
% 2.20/0.67    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 2.20/0.67    inference(definition_unfolding,[],[f31,f53,f53])).
% 2.20/0.67  fof(f31,plain,(
% 2.20/0.67    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 2.20/0.67    inference(cnf_transformation,[],[f17])).
% 2.20/0.67  fof(f429,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X2),X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.20/0.67    inference(forward_demodulation,[],[f428,f78])).
% 2.20/0.67  fof(f428,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X2),X0),k2_relat_1(k7_relat_1(sK2,X1)))) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f427,f30])).
% 2.20/0.67  fof(f427,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(sK2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X2),X0),k2_relat_1(k7_relat_1(sK2,X1)))) )),
% 2.20/0.67    inference(duplicate_literal_removal,[],[f422])).
% 2.20/0.67  fof(f422,plain,(
% 2.20/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(sK2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X2),X0),k2_relat_1(k7_relat_1(sK2,X1))) | ~v1_relat_1(sK2)) )),
% 2.20/0.67    inference(resolution,[],[f277,f39])).
% 2.20/0.67  fof(f277,plain,(
% 2.20/0.67    ( ! [X2,X0,X3,X1] : (~r1_tarski(k7_relat_1(sK2,X1),X0) | ~v1_relat_1(X0) | ~r1_tarski(X2,X3) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k2_relat_1(k7_relat_1(X0,X3)))) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f276,f38])).
% 2.20/0.67  fof(f276,plain,(
% 2.20/0.67    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r1_tarski(k7_relat_1(sK2,X1),X0) | ~r1_tarski(X2,X3) | ~v1_relat_1(k7_relat_1(X0,X3)) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k2_relat_1(k7_relat_1(X0,X3)))) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f266,f68])).
% 2.20/0.67  fof(f266,plain,(
% 2.20/0.67    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r1_tarski(k7_relat_1(sK2,X1),X0) | ~r1_tarski(X2,X3) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(X0,X3)) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k2_relat_1(k7_relat_1(X0,X3)))) )),
% 2.20/0.67    inference(resolution,[],[f45,f124])).
% 2.20/0.67  fof(f124,plain,(
% 2.20/0.67    ( ! [X12,X13,X11] : (~r1_tarski(k7_relat_1(k7_relat_1(sK2,X11),X12),X13) | ~v1_relat_1(X13) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X11),X12),k2_relat_1(X13))) )),
% 2.20/0.67    inference(subsumption_resolution,[],[f120,f68])).
% 2.20/0.67  fof(f120,plain,(
% 2.20/0.67    ( ! [X12,X13,X11] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X11),X12),k2_relat_1(X13)) | ~v1_relat_1(X13) | ~r1_tarski(k7_relat_1(k7_relat_1(sK2,X11),X12),X13) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,X11),X12))) )),
% 2.20/0.67    inference(superposition,[],[f33,f109])).
% 2.20/0.67  fof(f45,plain,(
% 2.20/0.67    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~v1_relat_1(X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f27])).
% 2.20/0.67  fof(f27,plain,(
% 2.20/0.67    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 2.20/0.67    inference(flattening,[],[f26])).
% 2.20/0.67  fof(f26,plain,(
% 2.20/0.67    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 2.20/0.67    inference(ennf_transformation,[],[f10])).
% 2.20/0.67  fof(f10,axiom,(
% 2.20/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 2.20/0.67  fof(f576,plain,(
% 2.20/0.67    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.20/0.67    inference(superposition,[],[f55,f574])).
% 2.20/0.67  fof(f55,plain,(
% 2.20/0.67    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 2.20/0.67    inference(definition_unfolding,[],[f35,f53])).
% 2.20/0.67  fof(f35,plain,(
% 2.20/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.20/0.67    inference(cnf_transformation,[],[f2])).
% 2.20/0.67  fof(f2,axiom,(
% 2.20/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.20/0.67  % SZS output end Proof for theBenchmark
% 2.20/0.67  % (14314)------------------------------
% 2.20/0.67  % (14314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.67  % (14314)Termination reason: Refutation
% 2.20/0.67  
% 2.20/0.67  % (14314)Memory used [KB]: 7164
% 2.20/0.67  % (14314)Time elapsed: 0.251 s
% 2.20/0.67  % (14314)------------------------------
% 2.20/0.67  % (14314)------------------------------
% 2.20/0.70  % (14306)Success in time 0.33 s
%------------------------------------------------------------------------------
