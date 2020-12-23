%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:41 EST 2020

% Result     : Theorem 3.59s
% Output     : Refutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 620 expanded)
%              Number of leaves         :   25 ( 169 expanded)
%              Depth                    :   22
%              Number of atoms          :  466 (2232 expanded)
%              Number of equality atoms :   93 ( 472 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f3586,f3620,f3904,f5304,f5340])).

fof(f5340,plain,
    ( spl12_2
    | ~ spl12_17 ),
    inference(avatar_contradiction_clause,[],[f5339])).

fof(f5339,plain,
    ( $false
    | spl12_2
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f98,f3976])).

fof(f3976,plain,
    ( r1_tarski(sK3,sK5)
    | ~ spl12_17 ),
    inference(trivial_inequality_removal,[],[f3936])).

fof(f3936,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,sK5)
    | ~ spl12_17 ),
    inference(superposition,[],[f56,f3869])).

fof(f3869,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK5)
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f3812,f112])).

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f60,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f3812,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,sK5),sK3)
    | k1_xboole_0 = k4_xboole_0(sK3,sK5)
    | ~ spl12_17 ),
    inference(superposition,[],[f52,f3681])).

fof(f3681,plain,
    ( sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))
    | ~ spl12_17 ),
    inference(resolution,[],[f3585,f146])).

fof(f146,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(X1,X2))
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f55,f112])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3585,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f3583])).

fof(f3583,plain,
    ( spl12_17
  <=> r1_tarski(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f98,plain,
    ( ~ r1_tarski(sK3,sK5)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl12_2
  <=> r1_tarski(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f5304,plain,
    ( spl12_1
    | spl12_8
    | ~ spl12_17 ),
    inference(avatar_contradiction_clause,[],[f5303])).

fof(f5303,plain,
    ( $false
    | spl12_1
    | spl12_8
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f5302,f94])).

fof(f94,plain,
    ( ~ r1_tarski(sK2,sK4)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl12_1
  <=> r1_tarski(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f5302,plain,
    ( r1_tarski(sK2,sK4)
    | spl12_8
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f5267,f119])).

fof(f119,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f112,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f83,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f5267,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(sK2,sK4)
    | spl12_8
    | ~ spl12_17 ),
    inference(superposition,[],[f151,f5234])).

fof(f5234,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK4)
    | spl12_8
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f5189,f112])).

fof(f5189,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK4),sK2)
    | k1_xboole_0 = k4_xboole_0(sK2,sK4)
    | spl12_8
    | ~ spl12_17 ),
    inference(superposition,[],[f52,f5156])).

fof(f5156,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
    | spl12_8
    | ~ spl12_17 ),
    inference(resolution,[],[f5152,f146])).

fof(f5152,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))
    | spl12_8
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f5151,f2347])).

fof(f2347,plain,
    ( k1_xboole_0 != sK3
    | spl12_8 ),
    inference(avatar_component_clause,[],[f2346])).

fof(f2346,plain,
    ( spl12_8
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f5151,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))
    | k1_xboole_0 = sK3
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f5134,f86])).

fof(f5134,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))
    | k1_xboole_0 = sK3
    | ~ spl12_17 ),
    inference(resolution,[],[f4112,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f4112,plain,
    ( ! [X2] :
        ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X2))
        | ~ r1_tarski(sK3,X2) )
    | ~ spl12_17 ),
    inference(forward_demodulation,[],[f4111,f49])).

fof(f4111,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k4_xboole_0(sK3,k1_xboole_0),X2)
        | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X2)) )
    | ~ spl12_17 ),
    inference(forward_demodulation,[],[f4110,f3869])).

fof(f4110,plain,(
    ! [X2] :
      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X2))
      | ~ r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),X2) ) ),
    inference(forward_demodulation,[],[f4055,f49])).

fof(f4055,plain,(
    ! [X2] :
      ( r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X2))
      | ~ r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),X2) ) ),
    inference(superposition,[],[f674,f111])).

fof(f111,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_tarski(sK3,sK5)
      | ~ r1_tarski(sK2,sK4) )
    & k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK3,sK5)
        | ~ r1_tarski(sK2,sK4) )
      & k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
      & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f674,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X10,X12),k4_xboole_0(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X13))),k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X14))
      | ~ r1_tarski(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X14) ) ),
    inference(superposition,[],[f59,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f82,f50,f50,f50])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X2,X3),k1_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(subsumption_resolution,[],[f143,f119])).

fof(f143,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3))
      | ~ r1_tarski(k4_xboole_0(X2,X3),k1_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(extensionality_resolution,[],[f55,f56])).

fof(f3904,plain,(
    ~ spl12_8 ),
    inference(avatar_contradiction_clause,[],[f3903])).

fof(f3903,plain,
    ( $false
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f3891,f119])).

fof(f3891,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl12_8 ),
    inference(backward_demodulation,[],[f753,f2348])).

fof(f2348,plain,
    ( k1_xboole_0 = sK3
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f2346])).

fof(f753,plain,(
    ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(resolution,[],[f743,f149])).

fof(f149,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f139,f119])).

fof(f139,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK3)) ),
    inference(extensionality_resolution,[],[f55,f46])).

fof(f46,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f743,plain,(
    ! [X6,X7] :
      ( r1_tarski(k2_zfmisc_1(X6,X7),k1_xboole_0)
      | ~ r1_tarski(X7,k1_xboole_0) ) ),
    inference(superposition,[],[f59,f737])).

fof(f737,plain,(
    ! [X9] : k1_xboole_0 = k2_zfmisc_1(X9,k1_xboole_0) ),
    inference(resolution,[],[f726,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f10,f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f726,plain,(
    ! [X0] : sP1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f596,f268])).

fof(f268,plain,(
    ! [X11] : ~ r2_hidden(X11,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f263,f244])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f62,f102])).

fof(f102,plain,(
    ! [X0] : sP0(X0,X0,k1_xboole_0) ),
    inference(superposition,[],[f88,f101])).

fof(f88,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f263,plain,(
    ! [X11] :
      ( ~ r2_hidden(X11,k1_xboole_0)
      | ~ r2_hidden(X11,k2_zfmisc_1(sK4,sK5)) ) ),
    inference(resolution,[],[f63,f181])).

fof(f181,plain,(
    sP0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[],[f88,f111])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f596,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(k1_xboole_0,X0,X1),X1)
      | sP1(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f75,f268])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
              & r2_hidden(sK9(X0,X1,X2),X0)
              & r2_hidden(sK8(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
                & r2_hidden(sK11(X0,X1,X8),X0)
                & r2_hidden(sK10(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X0)
        & r2_hidden(sK8(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
        & r2_hidden(sK11(X0,X1,X8),X0)
        & r2_hidden(sK10(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f3620,plain,(
    ~ spl12_14 ),
    inference(avatar_contradiction_clause,[],[f3619])).

fof(f3619,plain,
    ( $false
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f3595,f119])).

fof(f3595,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl12_14 ),
    inference(backward_demodulation,[],[f609,f2641])).

fof(f2641,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f2639])).

fof(f2639,plain,
    ( spl12_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f609,plain,(
    ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(resolution,[],[f560,f149])).

fof(f560,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X3,X2),k1_xboole_0)
      | ~ r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f58,f511])).

fof(f511,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(superposition,[],[f510,f49])).

fof(f510,plain,(
    ! [X8,X7] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k1_xboole_0,X7),X8) ),
    inference(resolution,[],[f503,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f503,plain,(
    ! [X14,X15] : sP0(X14,k2_zfmisc_1(k1_xboole_0,X15),k1_xboole_0) ),
    inference(resolution,[],[f474,f462])).

fof(f462,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f292,f268])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X2,X1,X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f70,f90])).

fof(f90,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X8,X2)
      | r2_hidden(sK10(X0,X1,X8),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f474,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,k1_xboole_0),X1)
      | sP0(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f65,f268])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3586,plain,
    ( spl12_14
    | spl12_17 ),
    inference(avatar_split_clause,[],[f3581,f3583,f2639])).

fof(f3581,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f3564,f112])).

fof(f3564,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),sK2)
    | r1_tarski(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1685,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1685,plain,(
    ! [X0] :
      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))))
      | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X0) ) ),
    inference(forward_demodulation,[],[f1658,f49])).

fof(f1658,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0),k2_zfmisc_1(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))))
      | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X0) ) ),
    inference(superposition,[],[f672,f111])).

fof(f672,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),k2_zfmisc_1(X4,k4_xboole_0(X2,k4_xboole_0(X2,X3))))
      | ~ r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X4) ) ),
    inference(superposition,[],[f58,f85])).

fof(f99,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f47,f96,f92])).

fof(f47,plain,
    ( ~ r1_tarski(sK3,sK5)
    | ~ r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (17776)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.49  % (17767)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.50  % (17775)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.50  % (17765)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.50  % (17790)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.50  % (17794)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (17769)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (17774)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.51  % (17777)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.51  % (17792)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.25/0.52  % (17786)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.25/0.52  % (17787)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.52  % (17782)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.25/0.52  % (17779)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.52  % (17766)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.52  % (17778)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.25/0.53  % (17783)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.25/0.53  % (17768)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.53  % (17772)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.25/0.53  % (17770)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.53  % (17771)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (17773)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.54  % (17788)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.40/0.54  % (17780)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.40/0.54  % (17793)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.54  % (17791)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % (17793)Refutation not found, incomplete strategy% (17793)------------------------------
% 1.40/0.54  % (17793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (17793)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (17793)Memory used [KB]: 10746
% 1.40/0.54  % (17793)Time elapsed: 0.150 s
% 1.40/0.54  % (17793)------------------------------
% 1.40/0.54  % (17793)------------------------------
% 1.40/0.54  % (17784)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.54  % (17785)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.55  % (17789)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.55  % (17775)Refutation not found, incomplete strategy% (17775)------------------------------
% 1.40/0.55  % (17775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (17781)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.55  % (17781)Refutation not found, incomplete strategy% (17781)------------------------------
% 1.40/0.55  % (17781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (17781)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (17781)Memory used [KB]: 10618
% 1.40/0.55  % (17781)Time elapsed: 0.155 s
% 1.40/0.55  % (17781)------------------------------
% 1.40/0.55  % (17781)------------------------------
% 1.40/0.56  % (17775)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (17775)Memory used [KB]: 11001
% 1.40/0.56  % (17775)Time elapsed: 0.147 s
% 1.40/0.56  % (17775)------------------------------
% 1.40/0.56  % (17775)------------------------------
% 2.10/0.68  % (17795)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.53/0.69  % (17796)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.53/0.71  % (17797)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.09/0.80  % (17767)Time limit reached!
% 3.09/0.80  % (17767)------------------------------
% 3.09/0.80  % (17767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.80  % (17767)Termination reason: Time limit
% 3.09/0.80  
% 3.09/0.80  % (17767)Memory used [KB]: 6780
% 3.09/0.80  % (17767)Time elapsed: 0.407 s
% 3.09/0.80  % (17767)------------------------------
% 3.09/0.80  % (17767)------------------------------
% 3.36/0.81  % (17789)Time limit reached!
% 3.36/0.81  % (17789)------------------------------
% 3.36/0.81  % (17789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.81  % (17789)Termination reason: Time limit
% 3.36/0.81  
% 3.36/0.81  % (17789)Memory used [KB]: 13944
% 3.36/0.81  % (17789)Time elapsed: 0.417 s
% 3.36/0.81  % (17789)------------------------------
% 3.36/0.81  % (17789)------------------------------
% 3.59/0.85  % (17771)Refutation found. Thanks to Tanya!
% 3.59/0.85  % SZS status Theorem for theBenchmark
% 3.59/0.85  % SZS output start Proof for theBenchmark
% 3.59/0.85  fof(f5341,plain,(
% 3.59/0.85    $false),
% 3.59/0.85    inference(avatar_sat_refutation,[],[f99,f3586,f3620,f3904,f5304,f5340])).
% 3.59/0.85  fof(f5340,plain,(
% 3.59/0.85    spl12_2 | ~spl12_17),
% 3.59/0.85    inference(avatar_contradiction_clause,[],[f5339])).
% 3.59/0.85  fof(f5339,plain,(
% 3.59/0.85    $false | (spl12_2 | ~spl12_17)),
% 3.59/0.85    inference(subsumption_resolution,[],[f98,f3976])).
% 3.59/0.85  fof(f3976,plain,(
% 3.59/0.85    r1_tarski(sK3,sK5) | ~spl12_17),
% 3.59/0.85    inference(trivial_inequality_removal,[],[f3936])).
% 3.59/0.85  fof(f3936,plain,(
% 3.59/0.85    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK3,sK5) | ~spl12_17),
% 3.59/0.85    inference(superposition,[],[f56,f3869])).
% 3.59/0.85  fof(f3869,plain,(
% 3.59/0.85    k1_xboole_0 = k4_xboole_0(sK3,sK5) | ~spl12_17),
% 3.59/0.85    inference(subsumption_resolution,[],[f3812,f112])).
% 3.59/0.85  fof(f112,plain,(
% 3.59/0.85    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.59/0.85    inference(resolution,[],[f60,f86])).
% 3.59/0.85  fof(f86,plain,(
% 3.59/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.85    inference(equality_resolution,[],[f54])).
% 3.59/0.85  fof(f54,plain,(
% 3.59/0.85    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.59/0.85    inference(cnf_transformation,[],[f30])).
% 3.59/0.85  fof(f30,plain,(
% 3.59/0.85    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.85    inference(flattening,[],[f29])).
% 3.59/0.85  fof(f29,plain,(
% 3.59/0.85    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.85    inference(nnf_transformation,[],[f2])).
% 3.59/0.85  fof(f2,axiom,(
% 3.59/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.59/0.85  fof(f60,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f21])).
% 3.59/0.85  fof(f21,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.59/0.85    inference(ennf_transformation,[],[f4])).
% 3.59/0.85  fof(f4,axiom,(
% 3.59/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.59/0.85  fof(f3812,plain,(
% 3.59/0.85    ~r1_tarski(k4_xboole_0(sK3,sK5),sK3) | k1_xboole_0 = k4_xboole_0(sK3,sK5) | ~spl12_17),
% 3.59/0.85    inference(superposition,[],[f52,f3681])).
% 3.59/0.85  fof(f3681,plain,(
% 3.59/0.85    sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) | ~spl12_17),
% 3.59/0.85    inference(resolution,[],[f3585,f146])).
% 3.59/0.85  fof(f146,plain,(
% 3.59/0.85    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(X1,X2)) | k4_xboole_0(X1,X2) = X1) )),
% 3.59/0.85    inference(resolution,[],[f55,f112])).
% 3.59/0.85  fof(f55,plain,(
% 3.59/0.85    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f30])).
% 3.59/0.85  fof(f3585,plain,(
% 3.59/0.85    r1_tarski(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) | ~spl12_17),
% 3.59/0.85    inference(avatar_component_clause,[],[f3583])).
% 3.59/0.85  fof(f3583,plain,(
% 3.59/0.85    spl12_17 <=> r1_tarski(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).
% 3.59/0.85  fof(f52,plain,(
% 3.59/0.85    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 3.59/0.85    inference(cnf_transformation,[],[f19])).
% 3.59/0.85  fof(f19,plain,(
% 3.59/0.85    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.59/0.85    inference(ennf_transformation,[],[f7])).
% 3.59/0.85  fof(f7,axiom,(
% 3.59/0.85    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 3.59/0.85  fof(f56,plain,(
% 3.59/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f31])).
% 3.59/0.85  fof(f31,plain,(
% 3.59/0.85    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.59/0.85    inference(nnf_transformation,[],[f3])).
% 3.59/0.85  fof(f3,axiom,(
% 3.59/0.85    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.59/0.85  fof(f98,plain,(
% 3.59/0.85    ~r1_tarski(sK3,sK5) | spl12_2),
% 3.59/0.85    inference(avatar_component_clause,[],[f96])).
% 3.59/0.85  fof(f96,plain,(
% 3.59/0.85    spl12_2 <=> r1_tarski(sK3,sK5)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 3.59/0.85  fof(f5304,plain,(
% 3.59/0.85    spl12_1 | spl12_8 | ~spl12_17),
% 3.59/0.85    inference(avatar_contradiction_clause,[],[f5303])).
% 3.59/0.85  fof(f5303,plain,(
% 3.59/0.85    $false | (spl12_1 | spl12_8 | ~spl12_17)),
% 3.59/0.85    inference(subsumption_resolution,[],[f5302,f94])).
% 3.59/0.85  fof(f94,plain,(
% 3.59/0.85    ~r1_tarski(sK2,sK4) | spl12_1),
% 3.59/0.85    inference(avatar_component_clause,[],[f92])).
% 3.59/0.85  fof(f92,plain,(
% 3.59/0.85    spl12_1 <=> r1_tarski(sK2,sK4)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 3.59/0.85  fof(f5302,plain,(
% 3.59/0.85    r1_tarski(sK2,sK4) | (spl12_8 | ~spl12_17)),
% 3.59/0.85    inference(subsumption_resolution,[],[f5267,f119])).
% 3.59/0.85  fof(f119,plain,(
% 3.59/0.85    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 3.59/0.85    inference(superposition,[],[f112,f101])).
% 3.59/0.85  fof(f101,plain,(
% 3.59/0.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.59/0.85    inference(forward_demodulation,[],[f83,f49])).
% 3.59/0.85  fof(f49,plain,(
% 3.59/0.85    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.59/0.85    inference(cnf_transformation,[],[f8])).
% 3.59/0.85  fof(f8,axiom,(
% 3.59/0.85    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.59/0.85  fof(f83,plain,(
% 3.59/0.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.59/0.85    inference(definition_unfolding,[],[f48,f50])).
% 3.59/0.85  fof(f50,plain,(
% 3.59/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f9])).
% 3.59/0.85  fof(f9,axiom,(
% 3.59/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.59/0.85  fof(f48,plain,(
% 3.59/0.85    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f6])).
% 3.59/0.85  fof(f6,axiom,(
% 3.59/0.85    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 3.59/0.85  fof(f5267,plain,(
% 3.59/0.85    ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(sK2,sK4) | (spl12_8 | ~spl12_17)),
% 3.59/0.85    inference(superposition,[],[f151,f5234])).
% 3.59/0.85  fof(f5234,plain,(
% 3.59/0.85    k1_xboole_0 = k4_xboole_0(sK2,sK4) | (spl12_8 | ~spl12_17)),
% 3.59/0.85    inference(subsumption_resolution,[],[f5189,f112])).
% 3.59/0.85  fof(f5189,plain,(
% 3.59/0.85    ~r1_tarski(k4_xboole_0(sK2,sK4),sK2) | k1_xboole_0 = k4_xboole_0(sK2,sK4) | (spl12_8 | ~spl12_17)),
% 3.59/0.85    inference(superposition,[],[f52,f5156])).
% 3.59/0.85  fof(f5156,plain,(
% 3.59/0.85    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) | (spl12_8 | ~spl12_17)),
% 3.59/0.85    inference(resolution,[],[f5152,f146])).
% 3.59/0.85  fof(f5152,plain,(
% 3.59/0.85    r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) | (spl12_8 | ~spl12_17)),
% 3.59/0.85    inference(subsumption_resolution,[],[f5151,f2347])).
% 3.59/0.85  fof(f2347,plain,(
% 3.59/0.85    k1_xboole_0 != sK3 | spl12_8),
% 3.59/0.85    inference(avatar_component_clause,[],[f2346])).
% 3.59/0.85  fof(f2346,plain,(
% 3.59/0.85    spl12_8 <=> k1_xboole_0 = sK3),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 3.59/0.85  fof(f5151,plain,(
% 3.59/0.85    r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) | k1_xboole_0 = sK3 | ~spl12_17),
% 3.59/0.85    inference(subsumption_resolution,[],[f5134,f86])).
% 3.59/0.85  fof(f5134,plain,(
% 3.59/0.85    ~r1_tarski(sK3,sK3) | r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) | k1_xboole_0 = sK3 | ~spl12_17),
% 3.59/0.85    inference(resolution,[],[f4112,f80])).
% 3.59/0.85  fof(f80,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 3.59/0.85    inference(cnf_transformation,[],[f22])).
% 3.59/0.85  fof(f22,plain,(
% 3.59/0.85    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 3.59/0.85    inference(ennf_transformation,[],[f11])).
% 3.59/0.85  fof(f11,axiom,(
% 3.59/0.85    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 3.59/0.85  fof(f4112,plain,(
% 3.59/0.85    ( ! [X2] : (r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X2)) | ~r1_tarski(sK3,X2)) ) | ~spl12_17),
% 3.59/0.85    inference(forward_demodulation,[],[f4111,f49])).
% 3.59/0.85  fof(f4111,plain,(
% 3.59/0.85    ( ! [X2] : (~r1_tarski(k4_xboole_0(sK3,k1_xboole_0),X2) | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X2))) ) | ~spl12_17),
% 3.59/0.85    inference(forward_demodulation,[],[f4110,f3869])).
% 3.59/0.85  fof(f4110,plain,(
% 3.59/0.85    ( ! [X2] : (r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X2)) | ~r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),X2)) )),
% 3.59/0.85    inference(forward_demodulation,[],[f4055,f49])).
% 3.59/0.85  fof(f4055,plain,(
% 3.59/0.85    ( ! [X2] : (r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X2)) | ~r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),X2)) )),
% 3.59/0.85    inference(superposition,[],[f674,f111])).
% 3.59/0.85  fof(f111,plain,(
% 3.59/0.85    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 3.59/0.85    inference(resolution,[],[f57,f45])).
% 3.59/0.85  fof(f45,plain,(
% 3.59/0.85    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 3.59/0.85    inference(cnf_transformation,[],[f28])).
% 3.59/0.85  fof(f28,plain,(
% 3.59/0.85    (~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)) & k1_xboole_0 != k2_zfmisc_1(sK2,sK3) & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 3.59/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f27])).
% 3.59/0.85  fof(f27,plain,(
% 3.59/0.85    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)) & k1_xboole_0 != k2_zfmisc_1(sK2,sK3) & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))),
% 3.59/0.85    introduced(choice_axiom,[])).
% 3.59/0.85  fof(f17,plain,(
% 3.59/0.85    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.59/0.85    inference(flattening,[],[f16])).
% 3.59/0.85  fof(f16,plain,(
% 3.59/0.85    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.59/0.85    inference(ennf_transformation,[],[f15])).
% 3.59/0.85  fof(f15,negated_conjecture,(
% 3.59/0.85    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.59/0.85    inference(negated_conjecture,[],[f14])).
% 3.59/0.85  fof(f14,conjecture,(
% 3.59/0.85    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 3.59/0.85  fof(f57,plain,(
% 3.59/0.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.59/0.85    inference(cnf_transformation,[],[f31])).
% 3.59/0.85  fof(f674,plain,(
% 3.59/0.85    ( ! [X14,X12,X10,X13,X11] : (r1_tarski(k4_xboole_0(k2_zfmisc_1(X10,X12),k4_xboole_0(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X13))),k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X14)) | ~r1_tarski(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X14)) )),
% 3.59/0.85    inference(superposition,[],[f59,f85])).
% 3.59/0.85  fof(f85,plain,(
% 3.59/0.85    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 3.59/0.85    inference(definition_unfolding,[],[f82,f50,f50,f50])).
% 3.59/0.85  fof(f82,plain,(
% 3.59/0.85    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f13])).
% 3.59/0.85  fof(f13,axiom,(
% 3.59/0.85    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 3.59/0.85  fof(f59,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f20])).
% 3.59/0.85  fof(f20,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.59/0.85    inference(ennf_transformation,[],[f12])).
% 3.59/0.85  fof(f12,axiom,(
% 3.59/0.85    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 3.59/0.85  fof(f151,plain,(
% 3.59/0.85    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X2,X3),k1_xboole_0) | r1_tarski(X2,X3)) )),
% 3.59/0.85    inference(subsumption_resolution,[],[f143,f119])).
% 3.59/0.85  fof(f143,plain,(
% 3.59/0.85    ( ! [X2,X3] : (~r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3)) | ~r1_tarski(k4_xboole_0(X2,X3),k1_xboole_0) | r1_tarski(X2,X3)) )),
% 3.59/0.85    inference(extensionality_resolution,[],[f55,f56])).
% 3.59/0.85  fof(f3904,plain,(
% 3.59/0.85    ~spl12_8),
% 3.59/0.85    inference(avatar_contradiction_clause,[],[f3903])).
% 3.59/0.85  fof(f3903,plain,(
% 3.59/0.85    $false | ~spl12_8),
% 3.59/0.85    inference(subsumption_resolution,[],[f3891,f119])).
% 3.59/0.85  fof(f3891,plain,(
% 3.59/0.85    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl12_8),
% 3.59/0.85    inference(backward_demodulation,[],[f753,f2348])).
% 3.59/0.85  fof(f2348,plain,(
% 3.59/0.85    k1_xboole_0 = sK3 | ~spl12_8),
% 3.59/0.85    inference(avatar_component_clause,[],[f2346])).
% 3.59/0.85  fof(f753,plain,(
% 3.59/0.85    ~r1_tarski(sK3,k1_xboole_0)),
% 3.59/0.85    inference(resolution,[],[f743,f149])).
% 3.59/0.85  fof(f149,plain,(
% 3.59/0.85    ~r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0)),
% 3.59/0.85    inference(subsumption_resolution,[],[f139,f119])).
% 3.59/0.85  fof(f139,plain,(
% 3.59/0.85    ~r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK3))),
% 3.59/0.85    inference(extensionality_resolution,[],[f55,f46])).
% 3.59/0.85  fof(f46,plain,(
% 3.59/0.85    k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 3.59/0.85    inference(cnf_transformation,[],[f28])).
% 3.59/0.85  fof(f743,plain,(
% 3.59/0.85    ( ! [X6,X7] : (r1_tarski(k2_zfmisc_1(X6,X7),k1_xboole_0) | ~r1_tarski(X7,k1_xboole_0)) )),
% 3.59/0.85    inference(superposition,[],[f59,f737])).
% 3.59/0.85  fof(f737,plain,(
% 3.59/0.85    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(X9,k1_xboole_0)) )),
% 3.59/0.85    inference(resolution,[],[f726,f79])).
% 3.59/0.85  fof(f79,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (~sP1(X1,X0,X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 3.59/0.85    inference(cnf_transformation,[],[f44])).
% 3.59/0.85  fof(f44,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 3.59/0.85    inference(nnf_transformation,[],[f26])).
% 3.59/0.85  fof(f26,plain,(
% 3.59/0.85    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 3.59/0.85    inference(definition_folding,[],[f10,f25])).
% 3.59/0.85  fof(f25,plain,(
% 3.59/0.85    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.59/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.59/0.85  fof(f10,axiom,(
% 3.59/0.85    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 3.59/0.85  fof(f726,plain,(
% 3.59/0.85    ( ! [X0] : (sP1(k1_xboole_0,X0,k1_xboole_0)) )),
% 3.59/0.85    inference(resolution,[],[f596,f268])).
% 3.59/0.85  fof(f268,plain,(
% 3.59/0.85    ( ! [X11] : (~r2_hidden(X11,k1_xboole_0)) )),
% 3.59/0.85    inference(subsumption_resolution,[],[f263,f244])).
% 3.59/0.85  fof(f244,plain,(
% 3.59/0.85    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 3.59/0.85    inference(resolution,[],[f62,f102])).
% 3.59/0.85  fof(f102,plain,(
% 3.59/0.85    ( ! [X0] : (sP0(X0,X0,k1_xboole_0)) )),
% 3.59/0.85    inference(superposition,[],[f88,f101])).
% 3.59/0.85  fof(f88,plain,(
% 3.59/0.85    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 3.59/0.85    inference(equality_resolution,[],[f68])).
% 3.59/0.85  fof(f68,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.59/0.85    inference(cnf_transformation,[],[f37])).
% 3.59/0.85  fof(f37,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 3.59/0.85    inference(nnf_transformation,[],[f24])).
% 3.59/0.85  fof(f24,plain,(
% 3.59/0.85    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.59/0.85    inference(definition_folding,[],[f1,f23])).
% 3.59/0.85  fof(f23,plain,(
% 3.59/0.85    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.59/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.59/0.85  fof(f1,axiom,(
% 3.59/0.85    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.59/0.85  fof(f62,plain,(
% 3.59/0.85    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f36])).
% 3.59/0.85  fof(f36,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 3.59/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 3.59/0.85  fof(f35,plain,(
% 3.59/0.85    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 3.59/0.85    introduced(choice_axiom,[])).
% 3.59/0.85  fof(f34,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 3.59/0.85    inference(rectify,[],[f33])).
% 3.59/0.85  fof(f33,plain,(
% 3.59/0.85    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.59/0.85    inference(flattening,[],[f32])).
% 3.59/0.85  fof(f32,plain,(
% 3.59/0.85    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.59/0.85    inference(nnf_transformation,[],[f23])).
% 3.59/0.85  fof(f263,plain,(
% 3.59/0.85    ( ! [X11] : (~r2_hidden(X11,k1_xboole_0) | ~r2_hidden(X11,k2_zfmisc_1(sK4,sK5))) )),
% 3.59/0.85    inference(resolution,[],[f63,f181])).
% 3.59/0.85  fof(f181,plain,(
% 3.59/0.85    sP0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK2,sK3),k1_xboole_0)),
% 3.59/0.85    inference(superposition,[],[f88,f111])).
% 3.59/0.85  fof(f63,plain,(
% 3.59/0.85    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f36])).
% 3.59/0.85  fof(f596,plain,(
% 3.59/0.85    ( ! [X0,X1] : (r2_hidden(sK7(k1_xboole_0,X0,X1),X1) | sP1(k1_xboole_0,X0,X1)) )),
% 3.59/0.85    inference(resolution,[],[f75,f268])).
% 3.59/0.85  fof(f75,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | sP1(X0,X1,X2)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f43])).
% 3.59/0.85  fof(f43,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X0) & r2_hidden(sK8(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X0) & r2_hidden(sK10(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP1(X0,X1,X2)))),
% 3.59/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f39,f42,f41,f40])).
% 3.59/0.85  fof(f40,plain,(
% 3.59/0.85    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 3.59/0.85    introduced(choice_axiom,[])).
% 3.59/0.85  fof(f41,plain,(
% 3.59/0.85    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X0) & r2_hidden(sK8(X0,X1,X2),X1)))),
% 3.59/0.85    introduced(choice_axiom,[])).
% 3.59/0.85  fof(f42,plain,(
% 3.59/0.85    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X0) & r2_hidden(sK10(X0,X1,X8),X1)))),
% 3.59/0.85    introduced(choice_axiom,[])).
% 3.59/0.85  fof(f39,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP1(X0,X1,X2)))),
% 3.59/0.85    inference(rectify,[],[f38])).
% 3.59/0.85  fof(f38,plain,(
% 3.59/0.85    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 3.59/0.85    inference(nnf_transformation,[],[f25])).
% 3.59/0.85  fof(f3620,plain,(
% 3.59/0.85    ~spl12_14),
% 3.59/0.85    inference(avatar_contradiction_clause,[],[f3619])).
% 3.59/0.85  fof(f3619,plain,(
% 3.59/0.85    $false | ~spl12_14),
% 3.59/0.85    inference(subsumption_resolution,[],[f3595,f119])).
% 3.59/0.85  fof(f3595,plain,(
% 3.59/0.85    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl12_14),
% 3.59/0.85    inference(backward_demodulation,[],[f609,f2641])).
% 3.59/0.85  fof(f2641,plain,(
% 3.59/0.85    k1_xboole_0 = sK2 | ~spl12_14),
% 3.59/0.85    inference(avatar_component_clause,[],[f2639])).
% 3.59/0.85  fof(f2639,plain,(
% 3.59/0.85    spl12_14 <=> k1_xboole_0 = sK2),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 3.59/0.85  fof(f609,plain,(
% 3.59/0.85    ~r1_tarski(sK2,k1_xboole_0)),
% 3.59/0.85    inference(resolution,[],[f560,f149])).
% 3.59/0.85  fof(f560,plain,(
% 3.59/0.85    ( ! [X2,X3] : (r1_tarski(k2_zfmisc_1(X3,X2),k1_xboole_0) | ~r1_tarski(X3,k1_xboole_0)) )),
% 3.59/0.85    inference(superposition,[],[f58,f511])).
% 3.59/0.85  fof(f511,plain,(
% 3.59/0.85    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 3.59/0.85    inference(superposition,[],[f510,f49])).
% 3.59/0.85  fof(f510,plain,(
% 3.59/0.85    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k1_xboole_0,X7),X8)) )),
% 3.59/0.85    inference(resolution,[],[f503,f69])).
% 3.59/0.85  fof(f69,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 3.59/0.85    inference(cnf_transformation,[],[f37])).
% 3.59/0.85  fof(f503,plain,(
% 3.59/0.85    ( ! [X14,X15] : (sP0(X14,k2_zfmisc_1(k1_xboole_0,X15),k1_xboole_0)) )),
% 3.59/0.85    inference(resolution,[],[f474,f462])).
% 3.59/0.85  fof(f462,plain,(
% 3.59/0.85    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 3.59/0.85    inference(resolution,[],[f292,f268])).
% 3.59/0.85  fof(f292,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (r2_hidden(sK10(X2,X1,X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.59/0.85    inference(resolution,[],[f70,f90])).
% 3.59/0.85  fof(f90,plain,(
% 3.59/0.85    ( ! [X0,X1] : (sP1(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 3.59/0.85    inference(equality_resolution,[],[f78])).
% 3.59/0.85  fof(f78,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.59/0.85    inference(cnf_transformation,[],[f44])).
% 3.59/0.85  fof(f70,plain,(
% 3.59/0.85    ( ! [X2,X0,X8,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X8,X2) | r2_hidden(sK10(X0,X1,X8),X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f43])).
% 3.59/0.85  fof(f474,plain,(
% 3.59/0.85    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,k1_xboole_0),X1) | sP0(X0,X1,k1_xboole_0)) )),
% 3.59/0.85    inference(resolution,[],[f65,f268])).
% 3.59/0.85  fof(f65,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f36])).
% 3.59/0.85  fof(f58,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f20])).
% 3.59/0.85  fof(f3586,plain,(
% 3.59/0.85    spl12_14 | spl12_17),
% 3.59/0.85    inference(avatar_split_clause,[],[f3581,f3583,f2639])).
% 3.59/0.85  fof(f3581,plain,(
% 3.59/0.85    r1_tarski(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) | k1_xboole_0 = sK2),
% 3.59/0.85    inference(subsumption_resolution,[],[f3564,f112])).
% 3.59/0.85  fof(f3564,plain,(
% 3.59/0.85    ~r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),sK2) | r1_tarski(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) | k1_xboole_0 = sK2),
% 3.59/0.85    inference(resolution,[],[f1685,f81])).
% 3.59/0.85  fof(f81,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 3.59/0.85    inference(cnf_transformation,[],[f22])).
% 3.59/0.85  fof(f1685,plain,(
% 3.59/0.85    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) | ~r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X0)) )),
% 3.59/0.85    inference(forward_demodulation,[],[f1658,f49])).
% 3.59/0.85  fof(f1658,plain,(
% 3.59/0.85    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0),k2_zfmisc_1(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) | ~r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X0)) )),
% 3.59/0.85    inference(superposition,[],[f672,f111])).
% 3.59/0.85  fof(f672,plain,(
% 3.59/0.85    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),k2_zfmisc_1(X4,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) | ~r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X4)) )),
% 3.59/0.85    inference(superposition,[],[f58,f85])).
% 3.59/0.85  fof(f99,plain,(
% 3.59/0.85    ~spl12_1 | ~spl12_2),
% 3.59/0.85    inference(avatar_split_clause,[],[f47,f96,f92])).
% 3.59/0.85  fof(f47,plain,(
% 3.59/0.85    ~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)),
% 3.59/0.85    inference(cnf_transformation,[],[f28])).
% 3.59/0.85  % SZS output end Proof for theBenchmark
% 3.59/0.85  % (17771)------------------------------
% 3.59/0.85  % (17771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.85  % (17771)Termination reason: Refutation
% 3.59/0.85  
% 3.59/0.85  % (17771)Memory used [KB]: 13432
% 3.59/0.85  % (17771)Time elapsed: 0.424 s
% 3.59/0.85  % (17771)------------------------------
% 3.59/0.85  % (17771)------------------------------
% 3.59/0.85  % (17764)Success in time 0.494 s
%------------------------------------------------------------------------------
