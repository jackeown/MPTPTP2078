%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0321+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (1714 expanded)
%              Number of leaves         :    5 ( 412 expanded)
%              Depth                    :   34
%              Number of atoms          :  180 (5208 expanded)
%              Number of equality atoms :   75 (3250 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(subsumption_resolution,[],[f209,f27])).

fof(f27,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f209,plain,(
    o_0_0_xboole_0 = sK1 ),
    inference(resolution,[],[f203,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f203,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(subsumption_resolution,[],[f202,f142])).

fof(f142,plain,(
    sK0 != sK2 ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,
    ( sK1 != sK1
    | sK0 != sK2 ),
    inference(superposition,[],[f14,f130])).

fof(f130,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f124,f27])).

fof(f124,plain,
    ( sK1 = sK3
    | o_0_0_xboole_0 = sK1 ),
    inference(resolution,[],[f122,f29])).

fof(f122,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK1 = sK3 ) ),
    inference(subsumption_resolution,[],[f119,f28])).

fof(f28,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f119,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK1 = sK3
      | o_0_0_xboole_0 = sK0 ) ),
    inference(resolution,[],[f103,f29])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1)
      | sK1 = sK3 ) ),
    inference(resolution,[],[f101,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f24,f15])).

fof(f15,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK1 = sK3 ) ),
    inference(condensation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | sK1 = sK3
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f95,f67])).

fof(f67,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f64,f24])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f59,f27])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | o_0_0_xboole_0 = sK1 ) ),
    inference(resolution,[],[f58,f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | o_0_0_xboole_0 = sK0 ) ),
    inference(resolution,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f32,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f31,f26])).

fof(f31,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK3) ) ),
    inference(superposition,[],[f25,f15])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK3)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X4,sK2) ) ),
    inference(superposition,[],[f26,f15])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK2)
      | sK1 = sK3 ) ),
    inference(subsumption_resolution,[],[f94,f82])).

fof(f82,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK1,sK3),sK1)
      | sK1 = sK3
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f63,f25])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2)
      | sK1 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | sK1 = sK3 ) ),
    inference(condensation,[],[f61])).

fof(f61,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(k4_tarski(X3,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(k4_tarski(X4,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | sK1 = sK3 ) ),
    inference(resolution,[],[f58,f39])).

fof(f39,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(X5,sK3),X5)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(k4_tarski(X4,sK5(X5,sK3)),k2_zfmisc_1(sK0,sK1))
      | sK3 = X5 ) ),
    inference(resolution,[],[f32,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f94,plain,(
    ! [X0,X1] :
      ( sK1 = sK3
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(sK1,sK3),sK1) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sK1 = sK3
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(sK1,sK3),sK1)
      | sK1 = sK3 ) ),
    inference(resolution,[],[f82,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,sK3),sK1)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(X0,sK3),X0)
      | sK3 = X0 ) ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f202,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = sK2 ) ),
    inference(subsumption_resolution,[],[f199,f198])).

fof(f198,plain,(
    r2_hidden(sK5(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f195,f142])).

fof(f195,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | sK0 = sK2 ),
    inference(factoring,[],[f189])).

fof(f189,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1,sK2),sK0)
      | sK2 = X1
      | r2_hidden(sK5(X1,sK2),X1) ) ),
    inference(resolution,[],[f179,f24])).

fof(f179,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(sK5(X2,sK2),X2)
      | sK2 = X2 ) ),
    inference(subsumption_resolution,[],[f178,f27])).

fof(f178,plain,(
    ! [X2] :
      ( o_0_0_xboole_0 = sK1
      | r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(sK5(X2,sK2),X2)
      | sK2 = X2 ) ),
    inference(forward_demodulation,[],[f177,f130])).

fof(f177,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | o_0_0_xboole_0 = sK3
      | r2_hidden(sK5(X2,sK2),X2)
      | sK2 = X2 ) ),
    inference(forward_demodulation,[],[f42,f130])).

fof(f42,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK3)),k2_zfmisc_1(sK0,sK1))
      | o_0_0_xboole_0 = sK3
      | r2_hidden(sK5(X2,sK2),X2)
      | sK2 = X2 ) ),
    inference(resolution,[],[f38,f21])).

fof(f38,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(k4_tarski(X3,sK4(sK3)),k2_zfmisc_1(sK0,sK1))
      | o_0_0_xboole_0 = sK3 ) ),
    inference(resolution,[],[f32,f29])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(sK0,sK2),sK0)
      | sK0 = sK2 ) ),
    inference(resolution,[],[f198,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X1,sK2),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(X1,sK2),X1)
      | sK2 = X1 ) ),
    inference(resolution,[],[f33,f22])).

%------------------------------------------------------------------------------
