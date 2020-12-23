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
% DateTime   : Thu Dec  3 12:52:28 EST 2020

% Result     : Theorem 5.72s
% Output     : Refutation 5.72s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 361 expanded)
%              Number of leaves         :   20 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  251 ( 657 expanded)
%              Number of equality atoms :   51 ( 177 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f95,f96,f138,f143,f148,f10863,f11157])).

fof(f11157,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f11133])).

fof(f11133,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f137,f11117])).

fof(f11117,plain,(
    ! [X4,X5] : r1_tarski(k6_relat_1(k3_xboole_0(X4,X5)),k7_relat_1(k6_relat_1(X4),X5)) ),
    inference(superposition,[],[f7725,f560])).

fof(f560,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X1) ),
    inference(resolution,[],[f553,f286])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f285,f104])).

fof(f104,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f57,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f283,f49])).

fof(f283,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(superposition,[],[f50,f54])).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f553,plain,(
    ! [X52,X53] : r1_tarski(k3_xboole_0(X53,X52),X52) ),
    inference(subsumption_resolution,[],[f552,f152])).

fof(f152,plain,(
    ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(subsumption_resolution,[],[f151,f49])).

fof(f151,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f133,f49])).

fof(f133,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X6))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f47,f104])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f552,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X53),X52))
      | r1_tarski(k3_xboole_0(X53,X52),X52) ) ),
    inference(forward_demodulation,[],[f551,f104])).

fof(f551,plain,(
    ! [X52,X53] :
      ( r1_tarski(k3_xboole_0(X53,X52),X52)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53))) ) ),
    inference(forward_demodulation,[],[f550,f108])).

fof(f108,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f106,f54])).

fof(f106,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f46,f49])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f550,plain,(
    ! [X52,X53] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X53),X52)),X52)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53))) ) ),
    inference(forward_demodulation,[],[f549,f104])).

fof(f549,plain,(
    ! [X52,X53] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53))),X52)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53))) ) ),
    inference(subsumption_resolution,[],[f526,f49])).

fof(f526,plain,(
    ! [X52,X53] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53))),X52)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53)))
      | ~ v1_relat_1(k6_relat_1(X52)) ) ),
    inference(resolution,[],[f496,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f496,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k6_relat_1(X0))
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f491,f49])).

fof(f491,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f52,f54])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f7725,plain,(
    ! [X4,X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(X2,X3)),X4),k7_relat_1(k6_relat_1(X2),X4)) ),
    inference(superposition,[],[f7519,f304])).

fof(f304,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(k3_xboole_0(X1,X2)),X1) ),
    inference(resolution,[],[f286,f109])).

fof(f109,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f74,f108])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(subsumption_resolution,[],[f73,f49])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f51,f54])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f7519,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f7496,f152])).

fof(f7496,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f62,f3728])).

fof(f3728,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f3725,f104])).

fof(f3725,plain,(
    ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f975,f49])).

fof(f975,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f56,f49])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f137,plain,
    ( ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_4
  <=> r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f10863,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f10841])).

fof(f10841,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f142,f10825])).

fof(f10825,plain,(
    ! [X28,X27] : r1_tarski(k7_relat_1(k6_relat_1(X27),X28),k6_relat_1(k3_xboole_0(X27,X28))) ),
    inference(superposition,[],[f7489,f10552])).

fof(f10552,plain,(
    ! [X33,X32] : k7_relat_1(k6_relat_1(X32),X33) = k7_relat_1(k7_relat_1(k6_relat_1(X32),X33),k3_xboole_0(X32,X33)) ),
    inference(resolution,[],[f10089,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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

fof(f10089,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X3),X4)
      | k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(backward_demodulation,[],[f287,f9869])).

fof(f9869,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(forward_demodulation,[],[f4600,f3728])).

fof(f4600,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f4599,f104])).

fof(f4599,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f4596,f104])).

fof(f4596,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(resolution,[],[f1752,f49])).

fof(f1752,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X1),k5_relat_1(X0,k6_relat_1(X2))) ) ),
    inference(resolution,[],[f176,f49])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X1,X0),k6_relat_1(X2)) = k5_relat_1(X1,k5_relat_1(X0,k6_relat_1(X2))) ) ),
    inference(resolution,[],[f48,f49])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f287,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X3),X4)
      | k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(subsumption_resolution,[],[f284,f152])).

fof(f284,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X3),X4)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))
      | k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(superposition,[],[f50,f108])).

fof(f7489,plain,(
    ! [X4,X2,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X2),X3),k6_relat_1(X3)) ),
    inference(backward_demodulation,[],[f201,f3728])).

fof(f201,plain,(
    ! [X4,X2,X3] : r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(X4)),k6_relat_1(X3)) ),
    inference(subsumption_resolution,[],[f195,f152])).

fof(f195,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(X4)),k6_relat_1(X3))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(resolution,[],[f162,f62])).

fof(f162,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k7_relat_1(k6_relat_1(X3),X4))
      | r1_tarski(X2,k6_relat_1(X4)) ) ),
    inference(resolution,[],[f150,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f150,plain,(
    ! [X4,X3] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f132,plain,(
    ! [X4,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f62,f104])).

fof(f142,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl2_5
  <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f148,plain,
    ( ~ spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f129,f69,f145])).

fof(f145,plain,
    ( spl2_6
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f69,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f129,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(superposition,[],[f71,f104])).

fof(f71,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f143,plain,
    ( ~ spl2_5
    | spl2_2 ),
    inference(avatar_split_clause,[],[f127,f88,f140])).

fof(f88,plain,
    ( spl2_2
  <=> r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f127,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(backward_demodulation,[],[f90,f104])).

fof(f90,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f138,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f126,f92,f135])).

fof(f92,plain,
    ( spl2_3
  <=> r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f126,plain,
    ( ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_3 ),
    inference(backward_demodulation,[],[f94,f104])).

fof(f94,plain,
    ( ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f96,plain,
    ( ~ spl2_3
    | ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f81,f69,f88,f92])).

fof(f81,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | spl2_1 ),
    inference(extensionality_resolution,[],[f61,f71])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f95,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f80,f69,f92,f88])).

fof(f80,plain,
    ( ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(extensionality_resolution,[],[f61,f71])).

fof(f72,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f45,f69])).

fof(f45,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (6952)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (6960)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (6953)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (6970)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (6970)Refutation not found, incomplete strategy% (6970)------------------------------
% 0.20/0.51  % (6970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6970)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6970)Memory used [KB]: 10618
% 0.20/0.51  % (6970)Time elapsed: 0.115 s
% 0.20/0.51  % (6970)------------------------------
% 0.20/0.51  % (6970)------------------------------
% 0.20/0.52  % (6956)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (6963)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (6969)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (6966)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (6954)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (6957)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (6958)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (6955)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (6979)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (6974)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (6979)Refutation not found, incomplete strategy% (6979)------------------------------
% 0.20/0.53  % (6979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6979)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6979)Memory used [KB]: 6140
% 0.20/0.53  % (6979)Time elapsed: 0.124 s
% 0.20/0.53  % (6979)------------------------------
% 0.20/0.53  % (6979)------------------------------
% 0.20/0.53  % (6965)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (6953)Refutation not found, incomplete strategy% (6953)------------------------------
% 0.20/0.53  % (6953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6953)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6953)Memory used [KB]: 1663
% 0.20/0.53  % (6953)Time elapsed: 0.122 s
% 0.20/0.53  % (6953)------------------------------
% 0.20/0.53  % (6953)------------------------------
% 0.20/0.53  % (6972)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (6977)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (6981)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (6981)Refutation not found, incomplete strategy% (6981)------------------------------
% 0.20/0.54  % (6981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6981)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6981)Memory used [KB]: 6140
% 0.20/0.54  % (6981)Time elapsed: 0.139 s
% 0.20/0.54  % (6981)------------------------------
% 0.20/0.54  % (6981)------------------------------
% 0.20/0.54  % (6980)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (6983)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (6976)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (6980)Refutation not found, incomplete strategy% (6980)------------------------------
% 0.20/0.54  % (6980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6980)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6980)Memory used [KB]: 6140
% 0.20/0.54  % (6980)Time elapsed: 0.136 s
% 0.20/0.54  % (6980)------------------------------
% 0.20/0.54  % (6980)------------------------------
% 0.20/0.54  % (6983)Refutation not found, incomplete strategy% (6983)------------------------------
% 0.20/0.54  % (6983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6983)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6983)Memory used [KB]: 1663
% 0.20/0.54  % (6983)Time elapsed: 0.138 s
% 0.20/0.54  % (6983)------------------------------
% 0.20/0.54  % (6983)------------------------------
% 0.20/0.54  % (6962)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (6963)Refutation not found, incomplete strategy% (6963)------------------------------
% 0.20/0.54  % (6963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6963)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6963)Memory used [KB]: 10746
% 0.20/0.54  % (6963)Time elapsed: 0.134 s
% 0.20/0.54  % (6963)------------------------------
% 0.20/0.54  % (6963)------------------------------
% 0.20/0.54  % (6975)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (6964)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (6964)Refutation not found, incomplete strategy% (6964)------------------------------
% 0.20/0.54  % (6964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6964)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6964)Memory used [KB]: 6140
% 0.20/0.54  % (6964)Time elapsed: 0.136 s
% 0.20/0.54  % (6964)------------------------------
% 0.20/0.54  % (6964)------------------------------
% 0.20/0.54  % (6978)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (6968)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (6973)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (6982)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (6982)Refutation not found, incomplete strategy% (6982)------------------------------
% 0.20/0.55  % (6982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6982)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6982)Memory used [KB]: 10746
% 0.20/0.55  % (6982)Time elapsed: 0.147 s
% 0.20/0.55  % (6982)------------------------------
% 0.20/0.55  % (6982)------------------------------
% 0.20/0.55  % (6968)Refutation not found, incomplete strategy% (6968)------------------------------
% 0.20/0.55  % (6968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6965)Refutation not found, incomplete strategy% (6965)------------------------------
% 0.20/0.55  % (6965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6965)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6965)Memory used [KB]: 10618
% 0.20/0.55  % (6965)Time elapsed: 0.150 s
% 0.20/0.55  % (6965)------------------------------
% 0.20/0.55  % (6965)------------------------------
% 0.20/0.55  % (6971)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (6968)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6968)Memory used [KB]: 1663
% 0.20/0.55  % (6968)Time elapsed: 0.146 s
% 0.20/0.55  % (6968)------------------------------
% 0.20/0.55  % (6968)------------------------------
% 0.20/0.55  % (6971)Refutation not found, incomplete strategy% (6971)------------------------------
% 0.20/0.55  % (6971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6959)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (6978)Refutation not found, incomplete strategy% (6978)------------------------------
% 0.20/0.55  % (6978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (6972)Refutation not found, incomplete strategy% (6972)------------------------------
% 0.20/0.56  % (6972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (6972)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (6972)Memory used [KB]: 1663
% 0.20/0.56  % (6972)Time elapsed: 0.157 s
% 0.20/0.56  % (6972)------------------------------
% 0.20/0.56  % (6972)------------------------------
% 0.20/0.56  % (6978)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (6978)Memory used [KB]: 10618
% 0.20/0.56  % (6978)Time elapsed: 0.123 s
% 0.20/0.56  % (6978)------------------------------
% 0.20/0.56  % (6978)------------------------------
% 0.20/0.56  % (6971)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (6971)Memory used [KB]: 1663
% 0.20/0.56  % (6971)Time elapsed: 0.130 s
% 0.20/0.56  % (6971)------------------------------
% 0.20/0.56  % (6971)------------------------------
% 2.16/0.64  % (7080)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.16/0.64  % (7070)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.66  % (7080)Refutation not found, incomplete strategy% (7080)------------------------------
% 2.16/0.66  % (7080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.66  % (7080)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.66  
% 2.16/0.66  % (7080)Memory used [KB]: 10618
% 2.16/0.66  % (7080)Time elapsed: 0.098 s
% 2.16/0.66  % (7080)------------------------------
% 2.16/0.66  % (7080)------------------------------
% 2.16/0.66  % (7075)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.16/0.66  % (6955)Refutation not found, incomplete strategy% (6955)------------------------------
% 2.16/0.66  % (6955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.66  % (6955)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.66  
% 2.16/0.66  % (6955)Memory used [KB]: 6140
% 2.16/0.66  % (6955)Time elapsed: 0.253 s
% 2.16/0.66  % (6955)------------------------------
% 2.16/0.66  % (6955)------------------------------
% 2.16/0.67  % (7096)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.16/0.67  % (7096)Refutation not found, incomplete strategy% (7096)------------------------------
% 2.16/0.67  % (7096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (7096)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.67  
% 2.16/0.67  % (7096)Memory used [KB]: 10746
% 2.16/0.67  % (7096)Time elapsed: 0.068 s
% 2.16/0.67  % (7096)------------------------------
% 2.16/0.67  % (7096)------------------------------
% 2.16/0.67  % (7083)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.16/0.67  % (7076)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.16/0.67  % (7088)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.16/0.68  % (7082)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.16/0.68  % (7083)Refutation not found, incomplete strategy% (7083)------------------------------
% 2.16/0.68  % (7083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (6969)Refutation not found, incomplete strategy% (6969)------------------------------
% 2.16/0.68  % (6969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (6969)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.68  
% 2.16/0.68  % (6969)Memory used [KB]: 6140
% 2.16/0.68  % (6969)Time elapsed: 0.245 s
% 2.16/0.68  % (6969)------------------------------
% 2.16/0.68  % (6969)------------------------------
% 2.16/0.68  % (7082)Refutation not found, incomplete strategy% (7082)------------------------------
% 2.16/0.68  % (7082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (7082)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.68  
% 2.16/0.68  % (7082)Memory used [KB]: 10618
% 2.16/0.68  % (7082)Time elapsed: 0.116 s
% 2.16/0.68  % (7082)------------------------------
% 2.16/0.68  % (7082)------------------------------
% 2.16/0.68  % (7092)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.16/0.68  % (7086)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.16/0.68  % (7083)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.68  
% 2.16/0.68  % (7083)Memory used [KB]: 1663
% 2.16/0.68  % (7083)Time elapsed: 0.117 s
% 2.16/0.68  % (7083)------------------------------
% 2.16/0.68  % (7083)------------------------------
% 2.16/0.68  % (7101)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.16/0.68  % (6954)Refutation not found, incomplete strategy% (6954)------------------------------
% 2.16/0.68  % (6954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.69  % (6954)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.69  
% 2.16/0.69  % (6954)Memory used [KB]: 6140
% 2.16/0.69  % (6954)Time elapsed: 0.287 s
% 2.16/0.69  % (6954)------------------------------
% 2.16/0.69  % (6954)------------------------------
% 2.16/0.69  % (7086)Refutation not found, incomplete strategy% (7086)------------------------------
% 2.16/0.69  % (7086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (7086)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (7086)Memory used [KB]: 10618
% 2.16/0.70  % (7086)Time elapsed: 0.135 s
% 2.16/0.70  % (7086)------------------------------
% 2.16/0.70  % (7086)------------------------------
% 2.16/0.70  % (7102)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.16/0.70  % (7102)Refutation not found, incomplete strategy% (7102)------------------------------
% 2.16/0.70  % (7102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (7102)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (7102)Memory used [KB]: 10618
% 2.16/0.70  % (7102)Time elapsed: 0.117 s
% 2.16/0.70  % (7102)------------------------------
% 2.16/0.70  % (7102)------------------------------
% 2.16/0.70  % (7097)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.76/0.71  % (7099)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.76/0.72  % (7099)Refutation not found, incomplete strategy% (7099)------------------------------
% 2.76/0.72  % (7099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.72  % (7099)Termination reason: Refutation not found, incomplete strategy
% 2.76/0.72  
% 2.76/0.72  % (7099)Memory used [KB]: 10618
% 2.76/0.72  % (7099)Time elapsed: 0.140 s
% 2.76/0.72  % (7099)------------------------------
% 2.76/0.72  % (7099)------------------------------
% 3.10/0.77  % (7130)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.10/0.77  % (7122)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.10/0.79  % (7127)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.10/0.79  % (7139)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.10/0.80  % (7132)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.10/0.81  % (7092)Refutation not found, incomplete strategy% (7092)------------------------------
% 3.10/0.81  % (7092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.81  % (7092)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.81  
% 3.10/0.81  % (7092)Memory used [KB]: 6268
% 3.10/0.81  % (7092)Time elapsed: 0.231 s
% 3.10/0.81  % (7092)------------------------------
% 3.10/0.81  % (7092)------------------------------
% 3.10/0.82  % (7135)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.10/0.82  % (7133)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.10/0.82  % (7135)Refutation not found, incomplete strategy% (7135)------------------------------
% 3.10/0.82  % (7135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.82  % (7135)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.82  
% 3.10/0.82  % (7135)Memory used [KB]: 1663
% 3.10/0.82  % (7135)Time elapsed: 0.121 s
% 3.10/0.82  % (7135)------------------------------
% 3.10/0.82  % (7135)------------------------------
% 3.70/0.87  % (7122)Refutation not found, incomplete strategy% (7122)------------------------------
% 3.70/0.87  % (7122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.88  % (7122)Termination reason: Refutation not found, incomplete strategy
% 3.70/0.88  
% 3.70/0.88  % (7122)Memory used [KB]: 6140
% 3.70/0.88  % (7122)Time elapsed: 0.179 s
% 3.70/0.88  % (7122)------------------------------
% 3.70/0.88  % (7122)------------------------------
% 3.94/0.90  % (7127)Refutation not found, incomplete strategy% (7127)------------------------------
% 3.94/0.90  % (7127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/0.91  % (7127)Termination reason: Refutation not found, incomplete strategy
% 3.94/0.91  
% 3.94/0.91  % (7127)Memory used [KB]: 6268
% 3.94/0.91  % (7127)Time elapsed: 0.201 s
% 3.94/0.91  % (7127)------------------------------
% 3.94/0.91  % (7127)------------------------------
% 3.94/0.91  % (6958)Time limit reached!
% 3.94/0.91  % (6958)------------------------------
% 3.94/0.91  % (6958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.92  % (6958)Termination reason: Time limit
% 4.25/0.92  % (6958)Termination phase: Saturation
% 4.25/0.92  
% 4.25/0.92  % (6958)Memory used [KB]: 17142
% 4.25/0.92  % (6958)Time elapsed: 0.500 s
% 4.25/0.92  % (6958)------------------------------
% 4.25/0.92  % (6958)------------------------------
% 4.79/1.05  % (6959)Time limit reached!
% 4.79/1.05  % (6959)------------------------------
% 4.79/1.05  % (6959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.06  % (6959)Termination reason: Time limit
% 4.79/1.06  % (6959)Termination phase: Saturation
% 4.79/1.06  
% 4.79/1.06  % (6959)Memory used [KB]: 6908
% 4.79/1.06  % (6959)Time elapsed: 0.600 s
% 4.79/1.06  % (6959)------------------------------
% 4.79/1.06  % (6959)------------------------------
% 5.72/1.12  % (6952)Refutation found. Thanks to Tanya!
% 5.72/1.12  % SZS status Theorem for theBenchmark
% 5.72/1.12  % (7132)Time limit reached!
% 5.72/1.12  % (7132)------------------------------
% 5.72/1.12  % (7132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.72/1.12  % (7132)Termination reason: Time limit
% 5.72/1.12  % (7132)Termination phase: Saturation
% 5.72/1.12  
% 5.72/1.12  % (7132)Memory used [KB]: 10490
% 5.72/1.12  % (7132)Time elapsed: 0.400 s
% 5.72/1.12  % (7132)------------------------------
% 5.72/1.12  % (7132)------------------------------
% 5.72/1.12  % SZS output start Proof for theBenchmark
% 5.72/1.12  fof(f11174,plain,(
% 5.72/1.12    $false),
% 5.72/1.12    inference(avatar_sat_refutation,[],[f72,f95,f96,f138,f143,f148,f10863,f11157])).
% 5.72/1.12  fof(f11157,plain,(
% 5.72/1.12    spl2_4),
% 5.72/1.12    inference(avatar_contradiction_clause,[],[f11133])).
% 5.72/1.12  fof(f11133,plain,(
% 5.72/1.12    $false | spl2_4),
% 5.72/1.12    inference(subsumption_resolution,[],[f137,f11117])).
% 5.72/1.12  fof(f11117,plain,(
% 5.72/1.12    ( ! [X4,X5] : (r1_tarski(k6_relat_1(k3_xboole_0(X4,X5)),k7_relat_1(k6_relat_1(X4),X5))) )),
% 5.72/1.12    inference(superposition,[],[f7725,f560])).
% 5.72/1.12  fof(f560,plain,(
% 5.72/1.12    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X1)) )),
% 5.72/1.12    inference(resolution,[],[f553,f286])).
% 5.72/1.12  fof(f286,plain,(
% 5.72/1.12    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 5.72/1.12    inference(forward_demodulation,[],[f285,f104])).
% 5.72/1.12  fof(f104,plain,(
% 5.72/1.12    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 5.72/1.12    inference(resolution,[],[f57,f49])).
% 5.72/1.12  fof(f49,plain,(
% 5.72/1.12    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 5.72/1.12    inference(cnf_transformation,[],[f11])).
% 5.72/1.12  fof(f11,axiom,(
% 5.72/1.12    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 5.72/1.12  fof(f57,plain,(
% 5.72/1.12    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 5.72/1.12    inference(cnf_transformation,[],[f39])).
% 5.72/1.12  fof(f39,plain,(
% 5.72/1.12    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 5.72/1.12    inference(ennf_transformation,[],[f25])).
% 5.72/1.12  fof(f25,axiom,(
% 5.72/1.12    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 5.72/1.12  fof(f285,plain,(
% 5.72/1.12    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f283,f49])).
% 5.72/1.12  fof(f283,plain,(
% 5.72/1.12    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 5.72/1.12    inference(superposition,[],[f50,f54])).
% 5.72/1.12  fof(f54,plain,(
% 5.72/1.12    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 5.72/1.12    inference(cnf_transformation,[],[f19])).
% 5.72/1.12  fof(f19,axiom,(
% 5.72/1.12    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 5.72/1.12  fof(f50,plain,(
% 5.72/1.12    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 5.72/1.12    inference(cnf_transformation,[],[f34])).
% 5.72/1.12  fof(f34,plain,(
% 5.72/1.12    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 5.72/1.12    inference(flattening,[],[f33])).
% 5.72/1.12  fof(f33,plain,(
% 5.72/1.12    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 5.72/1.12    inference(ennf_transformation,[],[f21])).
% 5.72/1.12  fof(f21,axiom,(
% 5.72/1.12    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 5.72/1.12  fof(f553,plain,(
% 5.72/1.12    ( ! [X52,X53] : (r1_tarski(k3_xboole_0(X53,X52),X52)) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f552,f152])).
% 5.72/1.12  fof(f152,plain,(
% 5.72/1.12    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f151,f49])).
% 5.72/1.12  fof(f151,plain,(
% 5.72/1.12    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f133,f49])).
% 5.72/1.12  fof(f133,plain,(
% 5.72/1.12    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 5.72/1.12    inference(superposition,[],[f47,f104])).
% 5.72/1.12  fof(f47,plain,(
% 5.72/1.12    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.72/1.12    inference(cnf_transformation,[],[f31])).
% 5.72/1.12  fof(f31,plain,(
% 5.72/1.12    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 5.72/1.12    inference(flattening,[],[f30])).
% 5.72/1.12  fof(f30,plain,(
% 5.72/1.12    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 5.72/1.12    inference(ennf_transformation,[],[f10])).
% 5.72/1.12  fof(f10,axiom,(
% 5.72/1.12    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 5.72/1.12  fof(f552,plain,(
% 5.72/1.12    ( ! [X52,X53] : (~v1_relat_1(k7_relat_1(k6_relat_1(X53),X52)) | r1_tarski(k3_xboole_0(X53,X52),X52)) )),
% 5.72/1.12    inference(forward_demodulation,[],[f551,f104])).
% 5.72/1.12  fof(f551,plain,(
% 5.72/1.12    ( ! [X52,X53] : (r1_tarski(k3_xboole_0(X53,X52),X52) | ~v1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53)))) )),
% 5.72/1.12    inference(forward_demodulation,[],[f550,f108])).
% 5.72/1.12  fof(f108,plain,(
% 5.72/1.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 5.72/1.12    inference(forward_demodulation,[],[f106,f54])).
% 5.72/1.12  fof(f106,plain,(
% 5.72/1.12    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 5.72/1.12    inference(resolution,[],[f46,f49])).
% 5.72/1.12  fof(f46,plain,(
% 5.72/1.12    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 5.72/1.12    inference(cnf_transformation,[],[f29])).
% 5.72/1.12  fof(f29,plain,(
% 5.72/1.12    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 5.72/1.12    inference(ennf_transformation,[],[f24])).
% 5.72/1.12  fof(f24,axiom,(
% 5.72/1.12    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 5.72/1.12  fof(f550,plain,(
% 5.72/1.12    ( ! [X52,X53] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X53),X52)),X52) | ~v1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53)))) )),
% 5.72/1.12    inference(forward_demodulation,[],[f549,f104])).
% 5.72/1.12  fof(f549,plain,(
% 5.72/1.12    ( ! [X52,X53] : (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53))),X52) | ~v1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53)))) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f526,f49])).
% 5.72/1.12  fof(f526,plain,(
% 5.72/1.12    ( ! [X52,X53] : (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53))),X52) | ~v1_relat_1(k5_relat_1(k6_relat_1(X52),k6_relat_1(X53))) | ~v1_relat_1(k6_relat_1(X52))) )),
% 5.72/1.12    inference(resolution,[],[f496,f62])).
% 5.72/1.12  fof(f62,plain,(
% 5.72/1.12    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 5.72/1.12    inference(cnf_transformation,[],[f42])).
% 5.72/1.12  fof(f42,plain,(
% 5.72/1.12    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 5.72/1.12    inference(ennf_transformation,[],[f20])).
% 5.72/1.12  fof(f20,axiom,(
% 5.72/1.12    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 5.72/1.12  fof(f496,plain,(
% 5.72/1.12    ( ! [X0,X1] : (~r1_tarski(X1,k6_relat_1(X0)) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f491,f49])).
% 5.72/1.12  fof(f491,plain,(
% 5.72/1.12    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 5.72/1.12    inference(superposition,[],[f52,f54])).
% 5.72/1.12  fof(f52,plain,(
% 5.72/1.12    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 5.72/1.12    inference(cnf_transformation,[],[f37])).
% 5.72/1.12  fof(f37,plain,(
% 5.72/1.12    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.72/1.12    inference(flattening,[],[f36])).
% 5.72/1.12  fof(f36,plain,(
% 5.72/1.12    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.72/1.12    inference(ennf_transformation,[],[f16])).
% 5.72/1.12  fof(f16,axiom,(
% 5.72/1.12    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 5.72/1.12  fof(f7725,plain,(
% 5.72/1.12    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(X2,X3)),X4),k7_relat_1(k6_relat_1(X2),X4))) )),
% 5.72/1.12    inference(superposition,[],[f7519,f304])).
% 5.72/1.12  fof(f304,plain,(
% 5.72/1.12    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(k3_xboole_0(X1,X2)),X1)) )),
% 5.72/1.12    inference(resolution,[],[f286,f109])).
% 5.72/1.12  fof(f109,plain,(
% 5.72/1.12    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 5.72/1.12    inference(backward_demodulation,[],[f74,f108])).
% 5.72/1.12  fof(f74,plain,(
% 5.72/1.12    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f73,f49])).
% 5.72/1.12  fof(f73,plain,(
% 5.72/1.12    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 5.72/1.12    inference(superposition,[],[f51,f54])).
% 5.72/1.12  fof(f51,plain,(
% 5.72/1.12    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 5.72/1.12    inference(cnf_transformation,[],[f35])).
% 5.72/1.12  fof(f35,plain,(
% 5.72/1.12    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 5.72/1.12    inference(ennf_transformation,[],[f23])).
% 5.72/1.12  fof(f23,axiom,(
% 5.72/1.12    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 5.72/1.12  fof(f7519,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1))) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f7496,f152])).
% 5.72/1.12  fof(f7496,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 5.72/1.12    inference(superposition,[],[f62,f3728])).
% 5.72/1.12  fof(f3728,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 5.72/1.12    inference(forward_demodulation,[],[f3725,f104])).
% 5.72/1.12  fof(f3725,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) )),
% 5.72/1.12    inference(resolution,[],[f975,f49])).
% 5.72/1.12  fof(f975,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1))) )),
% 5.72/1.12    inference(resolution,[],[f56,f49])).
% 5.72/1.12  fof(f56,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 5.72/1.12    inference(cnf_transformation,[],[f38])).
% 5.72/1.12  fof(f38,plain,(
% 5.72/1.12    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 5.72/1.12    inference(ennf_transformation,[],[f12])).
% 5.72/1.12  fof(f12,axiom,(
% 5.72/1.12    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 5.72/1.12  fof(f137,plain,(
% 5.72/1.12    ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_4),
% 5.72/1.12    inference(avatar_component_clause,[],[f135])).
% 5.72/1.12  fof(f135,plain,(
% 5.72/1.12    spl2_4 <=> r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1))),
% 5.72/1.12    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 5.72/1.12  fof(f10863,plain,(
% 5.72/1.12    spl2_5),
% 5.72/1.12    inference(avatar_contradiction_clause,[],[f10841])).
% 5.72/1.12  fof(f10841,plain,(
% 5.72/1.12    $false | spl2_5),
% 5.72/1.12    inference(subsumption_resolution,[],[f142,f10825])).
% 5.72/1.12  fof(f10825,plain,(
% 5.72/1.12    ( ! [X28,X27] : (r1_tarski(k7_relat_1(k6_relat_1(X27),X28),k6_relat_1(k3_xboole_0(X27,X28)))) )),
% 5.72/1.12    inference(superposition,[],[f7489,f10552])).
% 5.72/1.12  fof(f10552,plain,(
% 5.72/1.12    ( ! [X33,X32] : (k7_relat_1(k6_relat_1(X32),X33) = k7_relat_1(k7_relat_1(k6_relat_1(X32),X33),k3_xboole_0(X32,X33))) )),
% 5.72/1.12    inference(resolution,[],[f10089,f66])).
% 5.72/1.12  fof(f66,plain,(
% 5.72/1.12    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.72/1.12    inference(equality_resolution,[],[f60])).
% 5.72/1.12  fof(f60,plain,(
% 5.72/1.12    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.72/1.12    inference(cnf_transformation,[],[f1])).
% 5.72/1.12  fof(f1,axiom,(
% 5.72/1.12    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.72/1.12  fof(f10089,plain,(
% 5.72/1.12    ( ! [X4,X2,X3] : (~r1_tarski(k3_xboole_0(X2,X3),X4) | k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4)) )),
% 5.72/1.12    inference(backward_demodulation,[],[f287,f9869])).
% 5.72/1.12  fof(f9869,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) )),
% 5.72/1.12    inference(forward_demodulation,[],[f4600,f3728])).
% 5.72/1.12  fof(f4600,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 5.72/1.12    inference(forward_demodulation,[],[f4599,f104])).
% 5.72/1.12  fof(f4599,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 5.72/1.12    inference(forward_demodulation,[],[f4596,f104])).
% 5.72/1.12  fof(f4596,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 5.72/1.12    inference(resolution,[],[f1752,f49])).
% 5.72/1.12  fof(f1752,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X1),k5_relat_1(X0,k6_relat_1(X2)))) )),
% 5.72/1.12    inference(resolution,[],[f176,f49])).
% 5.72/1.12  fof(f176,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X1,X0),k6_relat_1(X2)) = k5_relat_1(X1,k5_relat_1(X0,k6_relat_1(X2)))) )),
% 5.72/1.12    inference(resolution,[],[f48,f49])).
% 5.72/1.12  fof(f48,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 5.72/1.12    inference(cnf_transformation,[],[f32])).
% 5.72/1.12  fof(f32,plain,(
% 5.72/1.12    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.72/1.12    inference(ennf_transformation,[],[f18])).
% 5.72/1.12  fof(f18,axiom,(
% 5.72/1.12    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 5.72/1.12  fof(f287,plain,(
% 5.72/1.12    ( ! [X4,X2,X3] : (~r1_tarski(k3_xboole_0(X2,X3),X4) | k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X2),X3))) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f284,f152])).
% 5.72/1.12  fof(f284,plain,(
% 5.72/1.12    ( ! [X4,X2,X3] : (~r1_tarski(k3_xboole_0(X2,X3),X4) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) | k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X2),X3))) )),
% 5.72/1.12    inference(superposition,[],[f50,f108])).
% 5.72/1.12  fof(f7489,plain,(
% 5.72/1.12    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X2),X3),k6_relat_1(X3))) )),
% 5.72/1.12    inference(backward_demodulation,[],[f201,f3728])).
% 5.72/1.12  fof(f201,plain,(
% 5.72/1.12    ( ! [X4,X2,X3] : (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(X4)),k6_relat_1(X3))) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f195,f152])).
% 5.72/1.12  fof(f195,plain,(
% 5.72/1.12    ( ! [X4,X2,X3] : (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(X4)),k6_relat_1(X3)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 5.72/1.12    inference(resolution,[],[f162,f62])).
% 5.72/1.12  fof(f162,plain,(
% 5.72/1.12    ( ! [X4,X2,X3] : (~r1_tarski(X2,k7_relat_1(k6_relat_1(X3),X4)) | r1_tarski(X2,k6_relat_1(X4))) )),
% 5.72/1.12    inference(resolution,[],[f150,f58])).
% 5.72/1.12  fof(f58,plain,(
% 5.72/1.12    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 5.72/1.12    inference(cnf_transformation,[],[f41])).
% 5.72/1.12  fof(f41,plain,(
% 5.72/1.12    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 5.72/1.12    inference(flattening,[],[f40])).
% 5.72/1.12  fof(f40,plain,(
% 5.72/1.12    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 5.72/1.12    inference(ennf_transformation,[],[f2])).
% 5.72/1.12  fof(f2,axiom,(
% 5.72/1.12    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 5.72/1.12  fof(f150,plain,(
% 5.72/1.12    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))) )),
% 5.72/1.12    inference(subsumption_resolution,[],[f132,f49])).
% 5.72/1.12  fof(f132,plain,(
% 5.72/1.12    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 5.72/1.12    inference(superposition,[],[f62,f104])).
% 5.72/1.12  fof(f142,plain,(
% 5.72/1.12    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k3_xboole_0(sK0,sK1))) | spl2_5),
% 5.72/1.12    inference(avatar_component_clause,[],[f140])).
% 5.72/1.12  fof(f140,plain,(
% 5.72/1.12    spl2_5 <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k3_xboole_0(sK0,sK1)))),
% 5.72/1.12    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 5.72/1.12  fof(f148,plain,(
% 5.72/1.12    ~spl2_6 | spl2_1),
% 5.72/1.12    inference(avatar_split_clause,[],[f129,f69,f145])).
% 5.72/1.12  fof(f145,plain,(
% 5.72/1.12    spl2_6 <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 5.72/1.12    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 5.72/1.12  fof(f69,plain,(
% 5.72/1.12    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 5.72/1.12    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 5.72/1.12  fof(f129,plain,(
% 5.72/1.12    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 5.72/1.12    inference(superposition,[],[f71,f104])).
% 5.72/1.12  fof(f71,plain,(
% 5.72/1.12    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 5.72/1.12    inference(avatar_component_clause,[],[f69])).
% 5.72/1.12  fof(f143,plain,(
% 5.72/1.12    ~spl2_5 | spl2_2),
% 5.72/1.12    inference(avatar_split_clause,[],[f127,f88,f140])).
% 5.72/1.12  fof(f88,plain,(
% 5.72/1.12    spl2_2 <=> r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1)))),
% 5.72/1.12    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 5.72/1.12  fof(f127,plain,(
% 5.72/1.12    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k3_xboole_0(sK0,sK1))) | spl2_2),
% 5.72/1.12    inference(backward_demodulation,[],[f90,f104])).
% 5.72/1.12  fof(f90,plain,(
% 5.72/1.12    ~r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1))) | spl2_2),
% 5.72/1.12    inference(avatar_component_clause,[],[f88])).
% 5.72/1.12  fof(f138,plain,(
% 5.72/1.12    ~spl2_4 | spl2_3),
% 5.72/1.12    inference(avatar_split_clause,[],[f126,f92,f135])).
% 5.72/1.12  fof(f92,plain,(
% 5.72/1.12    spl2_3 <=> r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))),
% 5.72/1.12    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 5.72/1.12  fof(f126,plain,(
% 5.72/1.12    ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_3),
% 5.72/1.12    inference(backward_demodulation,[],[f94,f104])).
% 5.72/1.12  fof(f94,plain,(
% 5.72/1.12    ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) | spl2_3),
% 5.72/1.12    inference(avatar_component_clause,[],[f92])).
% 5.72/1.12  fof(f96,plain,(
% 5.72/1.12    ~spl2_3 | ~spl2_2 | spl2_1),
% 5.72/1.12    inference(avatar_split_clause,[],[f81,f69,f88,f92])).
% 5.72/1.12  fof(f81,plain,(
% 5.72/1.12    ~r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1))) | ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) | spl2_1),
% 5.72/1.12    inference(extensionality_resolution,[],[f61,f71])).
% 5.72/1.12  fof(f61,plain,(
% 5.72/1.12    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 5.72/1.12    inference(cnf_transformation,[],[f1])).
% 5.72/1.12  fof(f95,plain,(
% 5.72/1.12    ~spl2_2 | ~spl2_3 | spl2_1),
% 5.72/1.12    inference(avatar_split_clause,[],[f80,f69,f92,f88])).
% 5.72/1.12  fof(f80,plain,(
% 5.72/1.12    ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) | ~r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1))) | spl2_1),
% 5.72/1.12    inference(extensionality_resolution,[],[f61,f71])).
% 5.72/1.12  fof(f72,plain,(
% 5.72/1.12    ~spl2_1),
% 5.72/1.12    inference(avatar_split_clause,[],[f45,f69])).
% 5.72/1.12  fof(f45,plain,(
% 5.72/1.12    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 5.72/1.12    inference(cnf_transformation,[],[f28])).
% 5.72/1.12  fof(f28,plain,(
% 5.72/1.12    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 5.72/1.12    inference(ennf_transformation,[],[f27])).
% 5.72/1.12  fof(f27,negated_conjecture,(
% 5.72/1.12    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 5.72/1.12    inference(negated_conjecture,[],[f26])).
% 5.72/1.12  fof(f26,conjecture,(
% 5.72/1.12    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 5.72/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 5.72/1.12  % SZS output end Proof for theBenchmark
% 5.72/1.12  % (6952)------------------------------
% 5.72/1.12  % (6952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.72/1.12  % (6952)Termination reason: Refutation
% 5.72/1.12  
% 5.72/1.12  % (6952)Memory used [KB]: 7675
% 5.72/1.12  % (6952)Time elapsed: 0.712 s
% 5.72/1.12  % (6952)------------------------------
% 5.72/1.12  % (6952)------------------------------
% 5.72/1.12  % (6948)Success in time 0.778 s
%------------------------------------------------------------------------------
