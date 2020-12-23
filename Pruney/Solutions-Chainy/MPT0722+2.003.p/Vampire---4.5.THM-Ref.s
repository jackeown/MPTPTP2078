%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 144 expanded)
%              Number of leaves         :    7 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 680 expanded)
%              Number of equality atoms :   23 ( 142 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0) ),
    inference(global_subsumption,[],[f21,f20,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
    & r1_tarski(sK1,k1_relat_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
            & r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(sK0))
          & v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
        & r1_tarski(X1,k1_relat_1(sK0))
        & v2_funct_1(sK0) )
   => ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
      & r1_tarski(sK1,k1_relat_1(sK0))
      & v2_funct_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ~ r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f43,f52])).

fof(f52,plain,(
    r1_tarski(sK1,k10_relat_1(sK0,k9_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X1] :
      ( ~ r1_tarski(k9_relat_1(sK0,sK1),X1)
      | r1_tarski(sK1,k10_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f48,f23])).

fof(f23,plain,(
    r1_tarski(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(sK0))
      | ~ r1_tarski(k9_relat_1(sK0,X0),X1)
      | r1_tarski(X0,k10_relat_1(sK0,X1)) ) ),
    inference(global_subsumption,[],[f20,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK0,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(sK0))
      | r1_tarski(X0,k10_relat_1(sK0,X1))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f30,f21])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f43,plain,
    ( ~ r1_tarski(sK1,k10_relat_1(sK0,k9_relat_1(sK0,sK1)))
    | ~ r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,sK1)),sK1) ),
    inference(forward_demodulation,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0) ),
    inference(global_subsumption,[],[f21,f20,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f26,f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f42,plain,
    ( ~ r1_tarski(sK1,k10_relat_1(sK0,k9_relat_1(sK0,sK1)))
    | ~ r1_tarski(k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)),sK1) ),
    inference(backward_demodulation,[],[f33,f41])).

fof(f33,plain,
    ( ~ r1_tarski(sK1,k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)))
    | ~ r1_tarski(k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)),sK1) ),
    inference(extensionality_resolution,[],[f29,f24])).

fof(f24,plain,(
    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:42:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.48  % (2392)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.48  % (2392)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(resolution,[],[f53,f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0)) )),
% 0.19/0.48    inference(global_subsumption,[],[f21,f20,f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.19/0.48    inference(resolution,[],[f25,f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    v2_funct_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    (sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) & r1_tarski(sK1,k1_relat_1(sK0)) & v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1 & r1_tarski(X1,k1_relat_1(sK0)) & v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ? [X1] : (k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1 & r1_tarski(X1,k1_relat_1(sK0)) & v2_funct_1(sK0)) => (sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) & r1_tarski(sK1,k1_relat_1(sK0)) & v2_funct_1(sK0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f8,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f7])).
% 0.19/0.48  fof(f7,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & (r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,negated_conjecture,(
% 0.19/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.19/0.48    inference(negated_conjecture,[],[f5])).
% 0.19/0.48  fof(f5,conjecture,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(flattening,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    v1_relat_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    v1_funct_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    ~r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,sK1)),sK1)),
% 0.19/0.48    inference(subsumption_resolution,[],[f43,f52])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    r1_tarski(sK1,k10_relat_1(sK0,k9_relat_1(sK0,sK1)))),
% 0.19/0.48    inference(resolution,[],[f50,f31])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.48    inference(equality_resolution,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(flattening,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    ( ! [X1] : (~r1_tarski(k9_relat_1(sK0,sK1),X1) | r1_tarski(sK1,k10_relat_1(sK0,X1))) )),
% 0.19/0.48    inference(resolution,[],[f48,f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    r1_tarski(sK1,k1_relat_1(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK0)) | ~r1_tarski(k9_relat_1(sK0,X0),X1) | r1_tarski(X0,k10_relat_1(sK0,X1))) )),
% 0.19/0.48    inference(global_subsumption,[],[f20,f47])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK0,X0),X1) | ~r1_tarski(X0,k1_relat_1(sK0)) | r1_tarski(X0,k10_relat_1(sK0,X1)) | ~v1_relat_1(sK0)) )),
% 0.19/0.48    inference(resolution,[],[f30,f21])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(flattening,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ~r1_tarski(sK1,k10_relat_1(sK0,k9_relat_1(sK0,sK1))) | ~r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,sK1)),sK1)),
% 0.19/0.48    inference(forward_demodulation,[],[f42,f41])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ( ! [X0] : (k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0)) )),
% 0.19/0.48    inference(global_subsumption,[],[f21,f20,f40])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ( ! [X0] : (k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.19/0.48    inference(resolution,[],[f26,f22])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(flattening,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ~r1_tarski(sK1,k10_relat_1(sK0,k9_relat_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)),sK1)),
% 0.19/0.48    inference(backward_demodulation,[],[f33,f41])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ~r1_tarski(sK1,k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)),sK1)),
% 0.19/0.48    inference(extensionality_resolution,[],[f29,f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (2392)------------------------------
% 0.19/0.48  % (2392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (2392)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (2392)Memory used [KB]: 6140
% 0.19/0.48  % (2392)Time elapsed: 0.073 s
% 0.19/0.48  % (2392)------------------------------
% 0.19/0.48  % (2392)------------------------------
% 0.19/0.49  % (2378)Success in time 0.137 s
%------------------------------------------------------------------------------
