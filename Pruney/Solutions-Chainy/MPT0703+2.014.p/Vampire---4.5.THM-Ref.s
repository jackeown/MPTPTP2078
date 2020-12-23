%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   16
%              Number of atoms          :  134 ( 423 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f673,plain,(
    $false ),
    inference(subsumption_resolution,[],[f672,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f672,plain,(
    ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f671,f54])).

fof(f54,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f671,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f659,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f659,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f151,f503])).

fof(f503,plain,(
    r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f402,f52])).

fof(f52,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f402,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),X1)
      | r1_tarski(sK0,k9_relat_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f399,f50])).

fof(f399,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k9_relat_1(sK2,X1))
      | ~ r1_tarski(k10_relat_1(sK2,sK0),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f76,f388])).

fof(f388,plain,(
    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f379,f124])).

fof(f124,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2))) ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f68,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f379,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(forward_demodulation,[],[f378,f91])).

fof(f91,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f59,f50])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f378,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f376,f50])).

fof(f376,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2))))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f81,f51])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f151,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X5,k9_relat_1(X4,k10_relat_1(X4,X6)))
      | ~ v1_relat_1(X4)
      | r1_tarski(X5,X6)
      | ~ v1_funct_1(X4) ) ),
    inference(resolution,[],[f70,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (28583)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (28583)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (28591)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f673,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f672,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f19])).
% 0.20/0.49  fof(f19,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.20/0.49  fof(f672,plain,(
% 0.20/0.49    ~v1_funct_1(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f671,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f671,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f659,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f659,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | r1_tarski(sK0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f151,f503])).
% 0.20/0.49  fof(f503,plain,(
% 0.20/0.49    r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 0.20/0.49    inference(resolution,[],[f402,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f402,plain,(
% 0.20/0.49    ( ! [X1] : (~r1_tarski(k10_relat_1(sK2,sK0),X1) | r1_tarski(sK0,k9_relat_1(sK2,X1))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f399,f50])).
% 0.20/0.49  fof(f399,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(sK0,k9_relat_1(sK2,X1)) | ~r1_tarski(k10_relat_1(sK2,sK0),X1) | ~v1_relat_1(sK2)) )),
% 0.20/0.49    inference(superposition,[],[f76,f388])).
% 0.20/0.49  fof(f388,plain,(
% 0.20/0.49    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.20/0.49    inference(superposition,[],[f379,f124])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2)))),
% 0.20/0.49    inference(resolution,[],[f80,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f68,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f60,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.50  fof(f379,plain,(
% 0.20/0.50    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f378,f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f59,f50])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2))))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f376,f50])).
% 0.20/0.50  fof(f376,plain,(
% 0.20/0.50    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) | ~v1_relat_1(sK2)) )),
% 0.20/0.50    inference(resolution,[],[f81,f51])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f71,f79])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ( ! [X6,X4,X5] : (~r1_tarski(X5,k9_relat_1(X4,k10_relat_1(X4,X6))) | ~v1_relat_1(X4) | r1_tarski(X5,X6) | ~v1_funct_1(X4)) )),
% 0.20/0.50    inference(resolution,[],[f70,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (28583)------------------------------
% 0.20/0.50  % (28583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28583)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (28583)Memory used [KB]: 11129
% 0.20/0.50  % (28583)Time elapsed: 0.091 s
% 0.20/0.50  % (28583)------------------------------
% 0.20/0.50  % (28583)------------------------------
% 0.20/0.50  % (28576)Success in time 0.141 s
%------------------------------------------------------------------------------
