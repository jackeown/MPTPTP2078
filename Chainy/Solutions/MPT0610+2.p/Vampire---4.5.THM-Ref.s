%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0610+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 11.63s
% Output     : Refutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :   25 (  40 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6767,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6766,f1196])).

fof(f1196,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f890])).

fof(f890,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f889])).

fof(f889,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f819])).

fof(f819,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f818])).

fof(f818,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

fof(f6766,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f6760,f1194])).

fof(f1194,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f890])).

fof(f6760,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f3457,f1284])).

fof(f1284,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f972])).

fof(f972,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f820])).

fof(f820,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f3457,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
      | ~ r1_xboole_0(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f3451,f1193])).

fof(f1193,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f890])).

fof(f3451,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
      | ~ r1_xboole_0(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f2098,f1284])).

fof(f2098,plain,(
    ! [X54,X52,X55,X53] :
      ( ~ r1_tarski(sK1,k2_zfmisc_1(X52,X53))
      | ~ r1_tarski(sK0,k2_zfmisc_1(X54,X55))
      | ~ r1_xboole_0(X54,X52) ) ),
    inference(resolution,[],[f1836,f1645])).

fof(f1645,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1147])).

fof(f1147,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f343])).

fof(f343,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1836,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X2,X1)
      | ~ r1_tarski(sK1,X1)
      | ~ r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f1195,f1199])).

fof(f1199,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f896])).

fof(f896,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f895])).

fof(f895,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f130])).

fof(f130,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f1195,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f890])).
%------------------------------------------------------------------------------
