%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:38 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 152 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   20
%              Number of atoms          :  191 ( 682 expanded)
%              Number of equality atoms :   32 ( 128 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(subsumption_resolution,[],[f77,f29])).

fof(f29,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f77,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f67,f27])).

fof(f27,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f58,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK1))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ) ),
    inference(subsumption_resolution,[],[f55,f25])).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f54,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK1))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(backward_demodulation,[],[f47,f50])).

fof(f50,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
    inference(subsumption_resolution,[],[f49,f25])).

fof(f49,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f48,f26])).

fof(f48,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(superposition,[],[f32,f46])).

fof(f46,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) ),
    inference(subsumption_resolution,[],[f45,f25])).

fof(f45,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f44,f26])).

% (31595)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f44,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f66,plain,(
    ! [X1] :
      ( r1_tarski(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))
      | ~ r1_tarski(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK1,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | r1_tarski(X0,k10_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f61,f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK1,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | r1_tarski(X0,k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f38,f26])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:31:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.37  ipcrm: permission denied for id (776830976)
% 0.20/0.37  ipcrm: permission denied for id (776896514)
% 0.20/0.37  ipcrm: permission denied for id (776929283)
% 0.20/0.38  ipcrm: permission denied for id (776962053)
% 0.20/0.38  ipcrm: permission denied for id (780632070)
% 0.20/0.38  ipcrm: permission denied for id (777027591)
% 0.20/0.38  ipcrm: permission denied for id (780664840)
% 0.20/0.38  ipcrm: permission denied for id (777093129)
% 0.20/0.38  ipcrm: permission denied for id (780697610)
% 0.20/0.38  ipcrm: permission denied for id (777158667)
% 0.20/0.38  ipcrm: permission denied for id (780730380)
% 0.20/0.39  ipcrm: permission denied for id (777191437)
% 0.20/0.39  ipcrm: permission denied for id (777224206)
% 0.20/0.39  ipcrm: permission denied for id (777256975)
% 0.20/0.39  ipcrm: permission denied for id (777289744)
% 0.20/0.39  ipcrm: permission denied for id (777322513)
% 0.20/0.39  ipcrm: permission denied for id (777355282)
% 0.20/0.39  ipcrm: permission denied for id (777388051)
% 0.20/0.39  ipcrm: permission denied for id (780763156)
% 0.20/0.40  ipcrm: permission denied for id (777453589)
% 0.20/0.40  ipcrm: permission denied for id (780795926)
% 0.20/0.40  ipcrm: permission denied for id (777519127)
% 0.20/0.40  ipcrm: permission denied for id (780828696)
% 0.20/0.40  ipcrm: permission denied for id (777584665)
% 0.20/0.40  ipcrm: permission denied for id (777650203)
% 0.20/0.40  ipcrm: permission denied for id (777682972)
% 0.20/0.41  ipcrm: permission denied for id (777715741)
% 0.20/0.41  ipcrm: permission denied for id (784269342)
% 0.20/0.41  ipcrm: permission denied for id (777748511)
% 0.20/0.41  ipcrm: permission denied for id (777781280)
% 0.20/0.41  ipcrm: permission denied for id (777814049)
% 0.20/0.41  ipcrm: permission denied for id (784334883)
% 0.20/0.41  ipcrm: permission denied for id (784367652)
% 0.20/0.42  ipcrm: permission denied for id (784400421)
% 0.20/0.42  ipcrm: permission denied for id (777977894)
% 0.20/0.42  ipcrm: permission denied for id (783089703)
% 0.20/0.42  ipcrm: permission denied for id (778043432)
% 0.20/0.42  ipcrm: permission denied for id (783122473)
% 0.20/0.42  ipcrm: permission denied for id (781123626)
% 0.20/0.42  ipcrm: permission denied for id (781156395)
% 0.20/0.42  ipcrm: permission denied for id (778141740)
% 0.20/0.43  ipcrm: permission denied for id (778174509)
% 0.20/0.43  ipcrm: permission denied for id (778207278)
% 0.20/0.43  ipcrm: permission denied for id (778240047)
% 0.20/0.43  ipcrm: permission denied for id (778272816)
% 0.20/0.43  ipcrm: permission denied for id (778305585)
% 0.20/0.43  ipcrm: permission denied for id (778338354)
% 0.20/0.43  ipcrm: permission denied for id (783155251)
% 0.20/0.43  ipcrm: permission denied for id (781221940)
% 0.20/0.44  ipcrm: permission denied for id (778436661)
% 0.20/0.44  ipcrm: permission denied for id (783188022)
% 0.20/0.44  ipcrm: permission denied for id (778502199)
% 0.20/0.44  ipcrm: permission denied for id (783220792)
% 0.20/0.44  ipcrm: permission denied for id (783253561)
% 0.20/0.44  ipcrm: permission denied for id (783286330)
% 0.20/0.44  ipcrm: permission denied for id (781385787)
% 0.20/0.44  ipcrm: permission denied for id (778633276)
% 0.20/0.45  ipcrm: permission denied for id (783319101)
% 0.20/0.45  ipcrm: permission denied for id (784433214)
% 0.20/0.45  ipcrm: permission denied for id (778698815)
% 0.20/0.45  ipcrm: permission denied for id (778731584)
% 0.20/0.45  ipcrm: permission denied for id (783384641)
% 0.20/0.45  ipcrm: permission denied for id (778797122)
% 0.20/0.45  ipcrm: permission denied for id (781516867)
% 0.20/0.45  ipcrm: permission denied for id (778862660)
% 0.20/0.46  ipcrm: permission denied for id (783417413)
% 0.20/0.46  ipcrm: permission denied for id (781582406)
% 0.20/0.46  ipcrm: permission denied for id (778993736)
% 0.20/0.46  ipcrm: permission denied for id (781647945)
% 0.20/0.46  ipcrm: permission denied for id (779059274)
% 0.20/0.46  ipcrm: permission denied for id (784498763)
% 0.20/0.46  ipcrm: permission denied for id (784531532)
% 0.20/0.47  ipcrm: permission denied for id (779124813)
% 0.20/0.47  ipcrm: permission denied for id (784564302)
% 0.20/0.47  ipcrm: permission denied for id (783581263)
% 0.20/0.47  ipcrm: permission denied for id (783614032)
% 0.20/0.47  ipcrm: permission denied for id (783646801)
% 0.20/0.47  ipcrm: permission denied for id (783679570)
% 0.20/0.47  ipcrm: permission denied for id (779255891)
% 0.20/0.47  ipcrm: permission denied for id (783712340)
% 0.20/0.48  ipcrm: permission denied for id (781942869)
% 0.20/0.48  ipcrm: permission denied for id (781975638)
% 0.20/0.48  ipcrm: permission denied for id (782008407)
% 0.20/0.48  ipcrm: permission denied for id (779386968)
% 0.20/0.48  ipcrm: permission denied for id (782041177)
% 0.20/0.48  ipcrm: permission denied for id (782073946)
% 0.20/0.48  ipcrm: permission denied for id (782106715)
% 0.20/0.49  ipcrm: permission denied for id (779485276)
% 0.20/0.49  ipcrm: permission denied for id (782139485)
% 0.20/0.49  ipcrm: permission denied for id (782172254)
% 0.20/0.49  ipcrm: permission denied for id (779583583)
% 0.20/0.49  ipcrm: permission denied for id (782205024)
% 0.20/0.49  ipcrm: permission denied for id (779649121)
% 0.20/0.49  ipcrm: permission denied for id (779681890)
% 0.20/0.49  ipcrm: permission denied for id (782237795)
% 0.20/0.50  ipcrm: permission denied for id (779747428)
% 0.20/0.50  ipcrm: permission denied for id (779780197)
% 0.20/0.50  ipcrm: permission denied for id (782270566)
% 0.20/0.50  ipcrm: permission denied for id (779845735)
% 0.20/0.50  ipcrm: permission denied for id (779878504)
% 0.20/0.50  ipcrm: permission denied for id (782303337)
% 0.20/0.50  ipcrm: permission denied for id (782336106)
% 0.20/0.50  ipcrm: permission denied for id (779976811)
% 0.20/0.50  ipcrm: permission denied for id (783745132)
% 0.20/0.51  ipcrm: permission denied for id (780042349)
% 0.20/0.51  ipcrm: permission denied for id (784597102)
% 0.20/0.51  ipcrm: permission denied for id (780107887)
% 0.20/0.51  ipcrm: permission denied for id (783810672)
% 0.20/0.51  ipcrm: permission denied for id (780173425)
% 0.20/0.51  ipcrm: permission denied for id (780206194)
% 0.20/0.52  ipcrm: permission denied for id (780271732)
% 0.20/0.52  ipcrm: permission denied for id (780304501)
% 0.20/0.52  ipcrm: permission denied for id (783876214)
% 0.20/0.52  ipcrm: permission denied for id (784662647)
% 0.20/0.52  ipcrm: permission denied for id (783941752)
% 0.20/0.52  ipcrm: permission denied for id (782631034)
% 0.20/0.52  ipcrm: permission denied for id (784007291)
% 0.20/0.53  ipcrm: permission denied for id (784072829)
% 0.20/0.53  ipcrm: permission denied for id (784138367)
% 0.55/0.64  % (31596)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.04/0.65  % (31614)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.04/0.65  % (31596)Refutation found. Thanks to Tanya!
% 1.04/0.65  % SZS status Theorem for theBenchmark
% 1.04/0.65  % SZS output start Proof for theBenchmark
% 1.04/0.65  fof(f79,plain,(
% 1.04/0.65    $false),
% 1.04/0.65    inference(subsumption_resolution,[],[f77,f29])).
% 1.04/0.65  fof(f29,plain,(
% 1.04/0.65    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.04/0.65    inference(cnf_transformation,[],[f22])).
% 1.04/0.65  fof(f22,plain,(
% 1.04/0.65    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.04/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21])).
% 1.04/0.65  fof(f21,plain,(
% 1.04/0.65    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.04/0.65    introduced(choice_axiom,[])).
% 1.04/0.65  fof(f10,plain,(
% 1.04/0.65    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.04/0.65    inference(flattening,[],[f9])).
% 1.04/0.65  fof(f9,plain,(
% 1.04/0.65    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.04/0.65    inference(ennf_transformation,[],[f8])).
% 1.04/0.65  fof(f8,negated_conjecture,(
% 1.04/0.65    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.04/0.65    inference(negated_conjecture,[],[f7])).
% 1.04/0.65  fof(f7,conjecture,(
% 1.04/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.04/0.65  fof(f77,plain,(
% 1.04/0.65    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.04/0.65    inference(resolution,[],[f67,f27])).
% 1.04/0.65  fof(f27,plain,(
% 1.04/0.65    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.04/0.65    inference(cnf_transformation,[],[f22])).
% 1.04/0.65  fof(f67,plain,(
% 1.04/0.65    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 1.04/0.65    inference(resolution,[],[f66,f60])).
% 1.04/0.65  fof(f60,plain,(
% 1.04/0.65    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 1.04/0.65    inference(resolution,[],[f59,f37])).
% 1.04/0.65  fof(f37,plain,(
% 1.04/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.04/0.65    inference(cnf_transformation,[],[f24])).
% 1.04/0.65  fof(f24,plain,(
% 1.04/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.04/0.65    inference(flattening,[],[f23])).
% 1.04/0.65  fof(f23,plain,(
% 1.04/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.04/0.65    inference(nnf_transformation,[],[f1])).
% 1.04/0.65  fof(f1,axiom,(
% 1.04/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.04/0.65  fof(f59,plain,(
% 1.04/0.65    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f58,f25])).
% 1.04/0.65  fof(f25,plain,(
% 1.04/0.65    v1_relat_1(sK1)),
% 1.04/0.65    inference(cnf_transformation,[],[f22])).
% 1.04/0.65  fof(f58,plain,(
% 1.04/0.65    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f57,f26])).
% 1.04/0.65  fof(f26,plain,(
% 1.04/0.65    v1_funct_1(sK1)),
% 1.04/0.65    inference(cnf_transformation,[],[f22])).
% 1.04/0.65  fof(f57,plain,(
% 1.04/0.65    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(resolution,[],[f56,f30])).
% 1.04/0.65  fof(f30,plain,(
% 1.04/0.65    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.04/0.65    inference(cnf_transformation,[],[f12])).
% 1.04/0.65  fof(f12,plain,(
% 1.04/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.04/0.65    inference(flattening,[],[f11])).
% 1.04/0.65  fof(f11,plain,(
% 1.04/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.04/0.65    inference(ennf_transformation,[],[f2])).
% 1.04/0.65  fof(f2,axiom,(
% 1.04/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.04/0.65  fof(f56,plain,(
% 1.04/0.65    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK1)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f55,f25])).
% 1.04/0.65  fof(f55,plain,(
% 1.04/0.65    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f54,f26])).
% 1.04/0.65  fof(f54,plain,(
% 1.04/0.65    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(resolution,[],[f51,f31])).
% 1.04/0.65  fof(f31,plain,(
% 1.04/0.65    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.04/0.65    inference(cnf_transformation,[],[f12])).
% 1.04/0.65  fof(f51,plain,(
% 1.04/0.65    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK1)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(k2_funct_1(sK1))) )),
% 1.04/0.65    inference(backward_demodulation,[],[f47,f50])).
% 1.04/0.65  fof(f50,plain,(
% 1.04/0.65    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f49,f25])).
% 1.04/0.65  fof(f49,plain,(
% 1.04/0.65    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f48,f26])).
% 1.04/0.65  fof(f48,plain,(
% 1.04/0.65    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(resolution,[],[f34,f28])).
% 1.04/0.65  fof(f28,plain,(
% 1.04/0.65    v2_funct_1(sK1)),
% 1.04/0.65    inference(cnf_transformation,[],[f22])).
% 1.04/0.65  fof(f34,plain,(
% 1.04/0.65    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.04/0.65    inference(cnf_transformation,[],[f18])).
% 1.04/0.65  fof(f18,plain,(
% 1.04/0.65    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.04/0.65    inference(flattening,[],[f17])).
% 1.04/0.65  fof(f17,plain,(
% 1.04/0.65    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.04/0.65    inference(ennf_transformation,[],[f5])).
% 1.04/0.65  fof(f5,axiom,(
% 1.04/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.04/0.65  fof(f47,plain,(
% 1.04/0.65    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))) )),
% 1.04/0.65    inference(superposition,[],[f32,f46])).
% 1.04/0.65  fof(f46,plain,(
% 1.04/0.65    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f45,f25])).
% 1.04/0.65  fof(f45,plain,(
% 1.04/0.65    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f44,f26])).
% 1.04/0.65  % (31595)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.04/0.65  fof(f44,plain,(
% 1.04/0.65    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(resolution,[],[f33,f28])).
% 1.04/0.65  fof(f33,plain,(
% 1.04/0.65    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.04/0.65    inference(cnf_transformation,[],[f16])).
% 1.04/0.65  fof(f16,plain,(
% 1.04/0.65    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.04/0.65    inference(flattening,[],[f15])).
% 1.04/0.65  fof(f15,plain,(
% 1.04/0.65    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.04/0.65    inference(ennf_transformation,[],[f4])).
% 1.04/0.65  fof(f4,axiom,(
% 1.04/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.04/0.65  fof(f32,plain,(
% 1.04/0.65    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.04/0.65    inference(cnf_transformation,[],[f14])).
% 1.04/0.65  fof(f14,plain,(
% 1.04/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.04/0.65    inference(flattening,[],[f13])).
% 1.04/0.65  fof(f13,plain,(
% 1.04/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.04/0.65    inference(ennf_transformation,[],[f3])).
% 1.04/0.65  fof(f3,axiom,(
% 1.04/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.04/0.65  fof(f66,plain,(
% 1.04/0.65    ( ! [X1] : (r1_tarski(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) | ~r1_tarski(X1,k1_relat_1(sK1))) )),
% 1.04/0.65    inference(resolution,[],[f63,f39])).
% 1.04/0.65  fof(f39,plain,(
% 1.04/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.04/0.65    inference(equality_resolution,[],[f36])).
% 1.04/0.65  fof(f36,plain,(
% 1.04/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.04/0.65    inference(cnf_transformation,[],[f24])).
% 1.04/0.65  fof(f63,plain,(
% 1.04/0.65    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK1,X0),X1) | ~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,X1))) )),
% 1.04/0.65    inference(subsumption_resolution,[],[f61,f25])).
% 1.04/0.65  fof(f61,plain,(
% 1.04/0.65    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK1,X0),X1) | ~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.04/0.65    inference(resolution,[],[f38,f26])).
% 1.04/0.65  fof(f38,plain,(
% 1.04/0.65    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.04/0.65    inference(cnf_transformation,[],[f20])).
% 1.04/0.65  fof(f20,plain,(
% 1.04/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.04/0.65    inference(flattening,[],[f19])).
% 1.04/0.65  fof(f19,plain,(
% 1.04/0.65    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.04/0.65    inference(ennf_transformation,[],[f6])).
% 1.04/0.65  fof(f6,axiom,(
% 1.04/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.04/0.65  % SZS output end Proof for theBenchmark
% 1.04/0.65  % (31596)------------------------------
% 1.04/0.65  % (31596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.04/0.65  % (31596)Termination reason: Refutation
% 1.04/0.65  
% 1.04/0.65  % (31596)Memory used [KB]: 6140
% 1.04/0.65  % (31596)Time elapsed: 0.035 s
% 1.04/0.65  % (31596)------------------------------
% 1.04/0.65  % (31596)------------------------------
% 1.04/0.65  % (31439)Success in time 0.288 s
%------------------------------------------------------------------------------
