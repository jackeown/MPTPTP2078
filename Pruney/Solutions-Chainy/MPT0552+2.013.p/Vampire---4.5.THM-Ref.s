%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 307 expanded)
%              Number of leaves         :   11 (  71 expanded)
%              Depth                    :   26
%              Number of atoms          :  190 ( 645 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1331,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1307,f44])).

% (7513)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1307,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f1266,f270])).

fof(f270,plain,(
    ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f187,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f117,f67])).

fof(f67,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0))
      | ~ r1_tarski(X1,k7_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f116,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k7_relat_1(sK2,X1))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k7_relat_1(sK2,X1)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f51,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK2) ),
    inference(resolution,[],[f33,f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f31,f27])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0))
      | ~ r1_tarski(X1,k7_relat_1(sK2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f112,f53])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0))
      | ~ r1_tarski(X1,k7_relat_1(sK2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f30,f67])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f187,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f104,f185])).

fof(f185,plain,(
    ! [X2,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X2)),k9_relat_1(sK2,X1)) ),
    inference(backward_demodulation,[],[f75,f184])).

fof(f184,plain,(
    ! [X4,X5] : k9_relat_1(k7_relat_1(sK2,X4),X5) = k9_relat_1(sK2,k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f157,f67])).

fof(f157,plain,(
    ! [X4,X5] : k9_relat_1(k7_relat_1(sK2,X4),X5) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X4,X5))) ),
    inference(backward_demodulation,[],[f69,f144])).

fof(f144,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f41,f27])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f69,plain,(
    ! [X4,X5] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X4),X5)) = k9_relat_1(k7_relat_1(sK2,X4),X5) ),
    inference(resolution,[],[f35,f53])).

fof(f75,plain,(
    ! [X2,X1] : r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k9_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f74,f69])).

fof(f74,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f72,f53])).

fof(f72,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f34,f67])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f104,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f28,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f1266,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X0,X1)),k7_relat_1(sK2,X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f1264])).

fof(f1264,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X0,X1)),k7_relat_1(sK2,X2))
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f1229,f43])).

fof(f1229,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X4,X4))
      | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X2,X3)),k7_relat_1(sK2,X4)) ) ),
    inference(forward_demodulation,[],[f1228,f144])).

fof(f1228,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X4))
      | ~ r1_tarski(X3,k3_xboole_0(X4,X4)) ) ),
    inference(resolution,[],[f600,f46])).

fof(f600,plain,(
    ! [X54,X55,X53] :
      ( ~ r1_tarski(X54,sK2)
      | r1_tarski(k7_relat_1(X54,X55),k7_relat_1(sK2,X53))
      | ~ r1_tarski(X55,k3_xboole_0(X53,X53)) ) ),
    inference(subsumption_resolution,[],[f599,f51])).

fof(f599,plain,(
    ! [X54,X55,X53] :
      ( r1_tarski(k7_relat_1(X54,X55),k7_relat_1(sK2,X53))
      | ~ r1_tarski(X54,sK2)
      | ~ r1_tarski(X55,k3_xboole_0(X53,X53))
      | ~ v1_relat_1(X54) ) ),
    inference(subsumption_resolution,[],[f580,f27])).

fof(f580,plain,(
    ! [X54,X55,X53] :
      ( r1_tarski(k7_relat_1(X54,X55),k7_relat_1(sK2,X53))
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(X54,sK2)
      | ~ r1_tarski(X55,k3_xboole_0(X53,X53))
      | ~ v1_relat_1(X54) ) ),
    inference(superposition,[],[f42,f534])).

fof(f534,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f533,f44])).

fof(f533,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f532,f44])).

fof(f532,plain,(
    ! [X0,X1] :
      ( k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f523,f43])).

fof(f523,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k3_xboole_0(X2,X3))
      | k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f522,f44])).

fof(f522,plain,(
    ! [X2,X3] :
      ( k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3))
      | ~ r1_tarski(sK2,sK2)
      | ~ r1_tarski(X2,k3_xboole_0(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f521,f27])).

fof(f521,plain,(
    ! [X2,X3] :
      ( k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3))
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(sK2,sK2)
      | ~ r1_tarski(X2,k3_xboole_0(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f518])).

fof(f518,plain,(
    ! [X2,X3] :
      ( k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3))
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(sK2,sK2)
      | ~ r1_tarski(X2,k3_xboole_0(X2,X3))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f183,f42])).

fof(f183,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK2,k3_xboole_0(X2,X3)))
      | k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3)) ) ),
    inference(forward_demodulation,[],[f155,f144])).

fof(f155,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK2,k3_xboole_0(X2,X3)))
      | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3) ) ),
    inference(backward_demodulation,[],[f63,f144])).

fof(f63,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(k7_relat_1(sK2,X2),X3))
      | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3) ) ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X2)) ),
    inference(resolution,[],[f53,f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

% (7506)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:31:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (7508)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (7516)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (7501)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (7510)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (7517)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  % (7518)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (7497)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (7499)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.55  % (7502)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.55  % (7519)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.55  % (7511)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.56  % (7522)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.56  % (7503)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.56  % (7498)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (7514)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.57  % (7504)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.57  % (7500)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.57  % (7520)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.58  % (7509)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.58  % (7516)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1331,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(subsumption_resolution,[],[f1307,f44])).
% 0.20/0.58  % (7513)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.58    inference(equality_resolution,[],[f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.58  fof(f1307,plain,(
% 0.20/0.58    ~r1_tarski(sK1,sK1)),
% 0.20/0.58    inference(resolution,[],[f1266,f270])).
% 0.20/0.58  fof(f270,plain,(
% 0.20/0.58    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))),
% 0.20/0.58    inference(resolution,[],[f187,f122])).
% 0.20/0.58  fof(f122,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) )),
% 0.20/0.58    inference(superposition,[],[f117,f67])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.20/0.58    inference(resolution,[],[f35,f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    v1_relat_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,plain,(
% 0.20/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.58    inference(negated_conjecture,[],[f12])).
% 0.20/0.58  fof(f12,conjecture,(
% 0.20/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.58  fof(f117,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0)) | ~r1_tarski(X1,k7_relat_1(sK2,X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f116,f56])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k7_relat_1(sK2,X1)) | v1_relat_1(X0)) )),
% 0.20/0.58    inference(resolution,[],[f54,f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k7_relat_1(sK2,X1))) | v1_relat_1(X0)) )),
% 0.20/0.58    inference(resolution,[],[f53,f31])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.20/0.58    inference(resolution,[],[f51,f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK2)) )),
% 0.20/0.58    inference(resolution,[],[f33,f27])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ( ! [X0] : (~r1_tarski(X0,sK2) | v1_relat_1(X0)) )),
% 0.20/0.58    inference(resolution,[],[f49,f39])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_relat_1(X0)) )),
% 0.20/0.58    inference(resolution,[],[f31,f27])).
% 0.20/0.58  fof(f116,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0)) | ~r1_tarski(X1,k7_relat_1(sK2,X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f112,f53])).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0)) | ~r1_tarski(X1,k7_relat_1(sK2,X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.58    inference(superposition,[],[f30,f67])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f15])).
% 0.20/0.58  fof(f15,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.58  fof(f187,plain,(
% 0.20/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 0.20/0.58    inference(subsumption_resolution,[],[f104,f185])).
% 0.20/0.58  fof(f185,plain,(
% 0.20/0.58    ( ! [X2,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X2)),k9_relat_1(sK2,X1))) )),
% 0.20/0.58    inference(backward_demodulation,[],[f75,f184])).
% 0.20/0.58  fof(f184,plain,(
% 0.20/0.58    ( ! [X4,X5] : (k9_relat_1(k7_relat_1(sK2,X4),X5) = k9_relat_1(sK2,k3_xboole_0(X4,X5))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f157,f67])).
% 0.20/0.58  fof(f157,plain,(
% 0.20/0.58    ( ! [X4,X5] : (k9_relat_1(k7_relat_1(sK2,X4),X5) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X4,X5)))) )),
% 0.20/0.58    inference(backward_demodulation,[],[f69,f144])).
% 0.20/0.58  fof(f144,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(resolution,[],[f41,f27])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X4,X5] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X4),X5)) = k9_relat_1(k7_relat_1(sK2,X4),X5)) )),
% 0.20/0.58    inference(resolution,[],[f35,f53])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X2,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k9_relat_1(sK2,X1))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f74,f69])).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),k9_relat_1(sK2,X1))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f72,f53])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),k9_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 0.20/0.58    inference(superposition,[],[f34,f67])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.20/0.58  fof(f104,plain,(
% 0.20/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 0.20/0.58    inference(resolution,[],[f28,f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.58    inference(flattening,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.58    inference(ennf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f1266,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X0,X1)),k7_relat_1(sK2,X2)) | ~r1_tarski(X1,X2)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f1264])).
% 0.20/0.58  fof(f1264,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X0,X1)),k7_relat_1(sK2,X2)) | ~r1_tarski(X1,X2) | ~r1_tarski(X1,X2)) )),
% 0.20/0.58    inference(resolution,[],[f1229,f43])).
% 0.20/0.58  fof(f1229,plain,(
% 0.20/0.58    ( ! [X4,X2,X3] : (~r1_tarski(X3,k3_xboole_0(X4,X4)) | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X2,X3)),k7_relat_1(sK2,X4))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f1228,f144])).
% 0.20/0.58  fof(f1228,plain,(
% 0.20/0.58    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X4)) | ~r1_tarski(X3,k3_xboole_0(X4,X4))) )),
% 0.20/0.58    inference(resolution,[],[f600,f46])).
% 0.20/0.58  fof(f600,plain,(
% 0.20/0.58    ( ! [X54,X55,X53] : (~r1_tarski(X54,sK2) | r1_tarski(k7_relat_1(X54,X55),k7_relat_1(sK2,X53)) | ~r1_tarski(X55,k3_xboole_0(X53,X53))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f599,f51])).
% 0.20/0.58  fof(f599,plain,(
% 0.20/0.58    ( ! [X54,X55,X53] : (r1_tarski(k7_relat_1(X54,X55),k7_relat_1(sK2,X53)) | ~r1_tarski(X54,sK2) | ~r1_tarski(X55,k3_xboole_0(X53,X53)) | ~v1_relat_1(X54)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f580,f27])).
% 0.20/0.58  fof(f580,plain,(
% 0.20/0.58    ( ! [X54,X55,X53] : (r1_tarski(k7_relat_1(X54,X55),k7_relat_1(sK2,X53)) | ~v1_relat_1(sK2) | ~r1_tarski(X54,sK2) | ~r1_tarski(X55,k3_xboole_0(X53,X53)) | ~v1_relat_1(X54)) )),
% 0.20/0.58    inference(superposition,[],[f42,f534])).
% 0.20/0.58  fof(f534,plain,(
% 0.20/0.58    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X0))) )),
% 0.20/0.58    inference(resolution,[],[f533,f44])).
% 0.20/0.58  fof(f533,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f532,f44])).
% 0.20/0.58  fof(f532,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0)) )),
% 0.20/0.58    inference(resolution,[],[f523,f43])).
% 0.20/0.58  fof(f523,plain,(
% 0.20/0.58    ( ! [X2,X3] : (~r1_tarski(X2,k3_xboole_0(X2,X3)) | k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f522,f44])).
% 0.20/0.58  fof(f522,plain,(
% 0.20/0.58    ( ! [X2,X3] : (k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3)) | ~r1_tarski(sK2,sK2) | ~r1_tarski(X2,k3_xboole_0(X2,X3))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f521,f27])).
% 0.20/0.58  fof(f521,plain,(
% 0.20/0.58    ( ! [X2,X3] : (k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3)) | ~v1_relat_1(sK2) | ~r1_tarski(sK2,sK2) | ~r1_tarski(X2,k3_xboole_0(X2,X3))) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f518])).
% 0.20/0.58  fof(f518,plain,(
% 0.20/0.58    ( ! [X2,X3] : (k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3)) | ~v1_relat_1(sK2) | ~r1_tarski(sK2,sK2) | ~r1_tarski(X2,k3_xboole_0(X2,X3)) | ~v1_relat_1(sK2)) )),
% 0.20/0.58    inference(resolution,[],[f183,f42])).
% 0.20/0.58  fof(f183,plain,(
% 0.20/0.58    ( ! [X2,X3] : (~r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK2,k3_xboole_0(X2,X3))) | k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X3))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f155,f144])).
% 0.20/0.58  fof(f155,plain,(
% 0.20/0.58    ( ! [X2,X3] : (~r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK2,k3_xboole_0(X2,X3))) | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f63,f144])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X2,X3] : (~r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(k7_relat_1(sK2,X2),X3)) | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3)) )),
% 0.20/0.58    inference(resolution,[],[f38,f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X2))) )),
% 0.20/0.58    inference(resolution,[],[f53,f33])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~v1_relat_1(X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.20/0.58    inference(flattening,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  % (7506)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (7516)------------------------------
% 0.20/0.58  % (7516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (7516)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (7516)Memory used [KB]: 2686
% 0.20/0.58  % (7516)Time elapsed: 0.148 s
% 0.20/0.58  % (7516)------------------------------
% 0.20/0.58  % (7516)------------------------------
% 0.20/0.58  % (7512)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.58  % (7496)Success in time 0.22 s
%------------------------------------------------------------------------------
