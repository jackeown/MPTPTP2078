%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1094+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:06 EST 2020

% Result     : Theorem 42.10s
% Output     : Refutation 42.10s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 264 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  175 (1051 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38057,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38056,f20196])).

fof(f20196,plain,(
    v1_finset_1(k1_relat_1(sK80)) ),
    inference(subsumption_resolution,[],[f20195,f5315])).

fof(f5315,plain,
    ( v1_finset_1(sK80)
    | v1_finset_1(k1_relat_1(sK80)) ),
    inference(cnf_transformation,[],[f3844])).

fof(f3844,plain,
    ( ( ~ v1_finset_1(sK80)
      | ~ v1_finset_1(k1_relat_1(sK80)) )
    & ( v1_finset_1(sK80)
      | v1_finset_1(k1_relat_1(sK80)) )
    & v1_funct_1(sK80)
    & v1_relat_1(sK80) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK80])],[f3842,f3843])).

fof(f3843,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(X0)
          | ~ v1_finset_1(k1_relat_1(X0)) )
        & ( v1_finset_1(X0)
          | v1_finset_1(k1_relat_1(X0)) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v1_finset_1(sK80)
        | ~ v1_finset_1(k1_relat_1(sK80)) )
      & ( v1_finset_1(sK80)
        | v1_finset_1(k1_relat_1(sK80)) )
      & v1_funct_1(sK80)
      & v1_relat_1(sK80) ) ),
    introduced(choice_axiom,[])).

fof(f3842,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f3841])).

fof(f3841,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1789])).

fof(f1789,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1788])).

fof(f1788,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1748])).

fof(f1748,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
        <=> v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1747])).

fof(f1747,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
      <=> v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).

fof(f20195,plain,
    ( v1_finset_1(k1_relat_1(sK80))
    | ~ v1_finset_1(sK80) ),
    inference(subsumption_resolution,[],[f20194,f6510])).

fof(f6510,plain,(
    ! [X0,X1] : v1_relat_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f1714])).

fof(f1714,axiom,(
    ! [X0,X1] :
      ( v1_funct_1(k7_funct_3(X0,X1))
      & v1_relat_1(k7_funct_3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_3)).

fof(f20194,plain,
    ( v1_finset_1(k1_relat_1(sK80))
    | ~ v1_finset_1(sK80)
    | ~ v1_relat_1(k7_funct_3(k1_relat_1(sK80),k2_relat_1(sK80))) ),
    inference(subsumption_resolution,[],[f20155,f6511])).

fof(f6511,plain,(
    ! [X0,X1] : v1_funct_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f1714])).

fof(f20155,plain,
    ( v1_finset_1(k1_relat_1(sK80))
    | ~ v1_finset_1(sK80)
    | ~ v1_funct_1(k7_funct_3(k1_relat_1(sK80),k2_relat_1(sK80)))
    | ~ v1_relat_1(k7_funct_3(k1_relat_1(sK80),k2_relat_1(sK80))) ),
    inference(superposition,[],[f7002,f9210])).

fof(f9210,plain,(
    k1_relat_1(sK80) = k9_relat_1(k7_funct_3(k1_relat_1(sK80),k2_relat_1(sK80)),sK80) ),
    inference(forward_demodulation,[],[f9209,f6441])).

fof(f6441,plain,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    inference(cnf_transformation,[],[f1732])).

fof(f1732,axiom,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

fof(f9209,plain,(
    k1_relat_1(sK80) = k9_relat_1(k9_funct_3(k1_relat_1(sK80),k2_relat_1(sK80)),sK80) ),
    inference(subsumption_resolution,[],[f9192,f5313])).

fof(f5313,plain,(
    v1_relat_1(sK80) ),
    inference(cnf_transformation,[],[f3844])).

fof(f9192,plain,
    ( k1_relat_1(sK80) = k9_relat_1(k9_funct_3(k1_relat_1(sK80),k2_relat_1(sK80)),sK80)
    | ~ v1_relat_1(sK80) ),
    inference(resolution,[],[f5314,f5971])).

fof(f5971,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2150])).

fof(f2150,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2149])).

fof(f2149,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1736])).

fof(f1736,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).

fof(f5314,plain,(
    v1_funct_1(sK80) ),
    inference(cnf_transformation,[],[f3844])).

fof(f7002,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2778])).

fof(f2778,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2777])).

fof(f2777,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1721])).

fof(f1721,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f38056,plain,(
    ~ v1_finset_1(k1_relat_1(sK80)) ),
    inference(subsumption_resolution,[],[f38049,f20360])).

fof(f20360,plain,(
    v1_finset_1(k2_relat_1(sK80)) ),
    inference(superposition,[],[f20202,f9098])).

fof(f9098,plain,(
    k2_relat_1(sK80) = k9_relat_1(sK80,k1_relat_1(sK80)) ),
    inference(resolution,[],[f5313,f5644])).

fof(f5644,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f1922])).

fof(f1922,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f748])).

fof(f748,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f20202,plain,(
    ! [X21] : v1_finset_1(k9_relat_1(sK80,X21)) ),
    inference(subsumption_resolution,[],[f19873,f20197])).

fof(f20197,plain,(
    ! [X34] : v1_finset_1(k1_relat_1(k7_relat_1(sK80,X34))) ),
    inference(subsumption_resolution,[],[f17602,f20196])).

fof(f17602,plain,(
    ! [X34] :
      ( v1_finset_1(k1_relat_1(k7_relat_1(sK80,X34)))
      | ~ v1_finset_1(k1_relat_1(sK80)) ) ),
    inference(superposition,[],[f6546,f9145])).

fof(f9145,plain,(
    ! [X43] : k3_xboole_0(k1_relat_1(sK80),X43) = k1_relat_1(k7_relat_1(sK80,X43)) ),
    inference(resolution,[],[f5313,f6586])).

fof(f6586,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f2386])).

fof(f2386,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f879])).

fof(f879,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f6546,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f2347])).

fof(f2347,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1739])).

fof(f1739,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).

fof(f19873,plain,(
    ! [X21] :
      ( v1_finset_1(k9_relat_1(sK80,X21))
      | ~ v1_finset_1(k1_relat_1(k7_relat_1(sK80,X21))) ) ),
    inference(subsumption_resolution,[],[f19872,f5313])).

fof(f19872,plain,(
    ! [X21] :
      ( v1_finset_1(k9_relat_1(sK80,X21))
      | ~ v1_finset_1(k1_relat_1(k7_relat_1(sK80,X21)))
      | ~ v1_relat_1(sK80) ) ),
    inference(subsumption_resolution,[],[f19832,f5314])).

fof(f19832,plain,(
    ! [X21] :
      ( v1_finset_1(k9_relat_1(sK80,X21))
      | ~ v1_finset_1(k1_relat_1(k7_relat_1(sK80,X21)))
      | ~ v1_funct_1(sK80)
      | ~ v1_relat_1(sK80) ) ),
    inference(superposition,[],[f7002,f9181])).

fof(f9181,plain,(
    ! [X46] : k9_relat_1(sK80,X46) = k9_relat_1(sK80,k1_relat_1(k7_relat_1(sK80,X46))) ),
    inference(forward_demodulation,[],[f9148,f9145])).

fof(f9148,plain,(
    ! [X46] : k9_relat_1(sK80,X46) = k9_relat_1(sK80,k3_xboole_0(k1_relat_1(sK80),X46)) ),
    inference(resolution,[],[f5313,f6589])).

fof(f6589,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f2389])).

fof(f2389,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f747])).

fof(f747,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f38049,plain,
    ( ~ v1_finset_1(k2_relat_1(sK80))
    | ~ v1_finset_1(k1_relat_1(sK80)) ),
    inference(resolution,[],[f20200,f6947])).

fof(f6947,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f2722])).

fof(f2722,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f2721])).

fof(f2721,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1722])).

fof(f1722,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).

fof(f20200,plain,(
    ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(sK80),k2_relat_1(sK80))) ),
    inference(subsumption_resolution,[],[f14767,f20199])).

fof(f20199,plain,(
    ~ v1_finset_1(sK80) ),
    inference(subsumption_resolution,[],[f5316,f20196])).

fof(f5316,plain,
    ( ~ v1_finset_1(k1_relat_1(sK80))
    | ~ v1_finset_1(sK80) ),
    inference(cnf_transformation,[],[f3844])).

fof(f14767,plain,
    ( v1_finset_1(sK80)
    | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(sK80),k2_relat_1(sK80))) ),
    inference(superposition,[],[f6545,f9103])).

fof(f9103,plain,(
    sK80 = k3_xboole_0(sK80,k2_zfmisc_1(k1_relat_1(sK80),k2_relat_1(sK80))) ),
    inference(resolution,[],[f5313,f5650])).

fof(f5650,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f1928])).

fof(f1928,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f826])).

fof(f826,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f6545,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f2346])).

fof(f2346,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(ennf_transformation,[],[f1718])).

fof(f1718,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).
%------------------------------------------------------------------------------
