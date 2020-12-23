%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:49 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 302 expanded)
%              Number of leaves         :    8 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  195 (1353 expanded)
%              Number of equality atoms :   71 ( 514 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(subsumption_resolution,[],[f93,f68])).

fof(f68,plain,(
    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(superposition,[],[f52,f63])).

fof(f63,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f61,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f60,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f59,f24])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
      | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f54,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_relat_1(sK0))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
      | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f29,f46])).

fof(f46,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f45,f42])).

fof(f42,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f41,f24])).

fof(f41,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f40,f25])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f31,f26])).

fof(f26,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f45,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f44,f24])).

fof(f44,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f43,f25])).

fof(f43,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f52,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f51,f42])).

fof(f51,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(forward_demodulation,[],[f27,f42])).

fof(f27,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f90,f24])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X0))
      | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f89,f24])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f58,f28])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_relat_1(sK0))
      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) ) ),
    inference(forward_demodulation,[],[f56,f50])).

fof(f50,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f49,f42])).

fof(f49,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f48,f24])).

fof(f48,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f47,f25])).

fof(f47,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f33,f26])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X0))
      | k2_relat_1(k4_relat_1(sK0)) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(sK0)) ) ),
    inference(superposition,[],[f30,f46])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n019.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 09:58:22 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.15/0.43  % (22719)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.15/0.44  % (22727)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.15/0.44  % (22719)Refutation not found, incomplete strategy% (22719)------------------------------
% 0.15/0.44  % (22719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.44  % (22719)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.44  
% 0.15/0.44  % (22719)Memory used [KB]: 6140
% 0.15/0.44  % (22719)Time elapsed: 0.065 s
% 0.15/0.44  % (22719)------------------------------
% 0.15/0.44  % (22719)------------------------------
% 0.15/0.44  % (22727)Refutation found. Thanks to Tanya!
% 0.15/0.44  % SZS status Theorem for theBenchmark
% 0.15/0.44  % SZS output start Proof for theBenchmark
% 0.15/0.44  fof(f94,plain,(
% 0.15/0.44    $false),
% 0.15/0.44    inference(subsumption_resolution,[],[f93,f68])).
% 0.15/0.44  fof(f68,plain,(
% 0.15/0.44    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.15/0.44    inference(trivial_inequality_removal,[],[f65])).
% 0.15/0.44  fof(f65,plain,(
% 0.15/0.44    k1_relat_1(sK0) != k1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.15/0.44    inference(superposition,[],[f52,f63])).
% 0.15/0.44  fof(f63,plain,(
% 0.15/0.44    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.15/0.44    inference(subsumption_resolution,[],[f61,f24])).
% 0.15/0.44  fof(f24,plain,(
% 0.15/0.44    v1_relat_1(sK0)),
% 0.15/0.44    inference(cnf_transformation,[],[f21])).
% 0.15/0.44  fof(f21,plain,(
% 0.15/0.44    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.15/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f20])).
% 0.15/0.44  fof(f20,plain,(
% 0.15/0.44    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.15/0.44    introduced(choice_axiom,[])).
% 0.15/0.44  fof(f10,plain,(
% 0.15/0.44    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.15/0.44    inference(flattening,[],[f9])).
% 0.15/0.44  fof(f9,plain,(
% 0.15/0.44    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.15/0.44    inference(ennf_transformation,[],[f8])).
% 0.15/0.44  fof(f8,negated_conjecture,(
% 0.15/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.15/0.44    inference(negated_conjecture,[],[f7])).
% 0.15/0.44  fof(f7,conjecture,(
% 0.15/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.15/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.15/0.44  fof(f61,plain,(
% 0.15/0.44    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.15/0.44    inference(resolution,[],[f60,f37])).
% 0.15/0.44  fof(f37,plain,(
% 0.15/0.44    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.15/0.44    inference(equality_resolution,[],[f35])).
% 0.15/0.44  fof(f35,plain,(
% 0.15/0.44    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.15/0.44    inference(cnf_transformation,[],[f23])).
% 0.15/0.44  fof(f23,plain,(
% 0.15/0.44    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.15/0.44    inference(flattening,[],[f22])).
% 0.15/0.44  fof(f22,plain,(
% 0.15/0.44    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.15/0.44    inference(nnf_transformation,[],[f1])).
% 0.15/0.44  fof(f1,axiom,(
% 0.15/0.44    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.15/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.15/0.45  fof(f60,plain,(
% 0.15/0.45    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) | ~v1_relat_1(X0)) )),
% 0.15/0.45    inference(subsumption_resolution,[],[f59,f24])).
% 0.15/0.45  fof(f59,plain,(
% 0.15/0.45    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) | ~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) )),
% 0.15/0.45    inference(resolution,[],[f54,f28])).
% 0.15/0.45  fof(f28,plain,(
% 0.15/0.45    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.15/0.45    inference(cnf_transformation,[],[f11])).
% 0.15/0.45  fof(f11,plain,(
% 0.15/0.45    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.15/0.45    inference(ennf_transformation,[],[f2])).
% 0.15/0.45  fof(f2,axiom,(
% 0.15/0.45    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.15/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.15/0.45  fof(f54,plain,(
% 0.15/0.45    ( ! [X0] : (~v1_relat_1(k4_relat_1(sK0)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) | ~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0)) )),
% 0.15/0.45    inference(superposition,[],[f29,f46])).
% 0.15/0.45  fof(f46,plain,(
% 0.15/0.45    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.15/0.45    inference(forward_demodulation,[],[f45,f42])).
% 0.15/0.45  fof(f42,plain,(
% 0.15/0.45    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.15/0.45    inference(subsumption_resolution,[],[f41,f24])).
% 0.15/0.45  fof(f41,plain,(
% 0.15/0.45    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.15/0.45    inference(subsumption_resolution,[],[f40,f25])).
% 0.15/0.45  fof(f25,plain,(
% 0.15/0.45    v1_funct_1(sK0)),
% 0.15/0.45    inference(cnf_transformation,[],[f21])).
% 0.15/0.45  fof(f40,plain,(
% 0.15/0.45    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.15/0.45    inference(resolution,[],[f31,f26])).
% 0.15/0.45  fof(f26,plain,(
% 0.15/0.45    v2_funct_1(sK0)),
% 0.15/0.45    inference(cnf_transformation,[],[f21])).
% 0.15/0.45  fof(f31,plain,(
% 0.15/0.45    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.15/0.45    inference(cnf_transformation,[],[f17])).
% 0.15/0.45  fof(f17,plain,(
% 0.15/0.45    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.15/0.45    inference(flattening,[],[f16])).
% 0.15/0.45  fof(f16,plain,(
% 0.15/0.45    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.15/0.45    inference(ennf_transformation,[],[f5])).
% 0.15/0.45  fof(f5,axiom,(
% 0.15/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.15/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.15/0.45  fof(f45,plain,(
% 0.15/0.45    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.15/0.45    inference(subsumption_resolution,[],[f44,f24])).
% 0.15/0.45  fof(f44,plain,(
% 0.15/0.45    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.15/0.45    inference(subsumption_resolution,[],[f43,f25])).
% 0.15/0.45  fof(f43,plain,(
% 0.15/0.45    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.15/0.45    inference(resolution,[],[f32,f26])).
% 0.15/0.45  fof(f32,plain,(
% 0.15/0.45    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.15/0.45    inference(cnf_transformation,[],[f19])).
% 0.15/0.45  fof(f19,plain,(
% 0.15/0.45    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.15/0.45    inference(flattening,[],[f18])).
% 0.15/0.45  fof(f18,plain,(
% 0.15/0.45    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.15/0.45    inference(ennf_transformation,[],[f6])).
% 0.15/0.45  fof(f6,axiom,(
% 0.15/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.15/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.15/0.45  fof(f29,plain,(
% 0.15/0.45    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.15/0.45    inference(cnf_transformation,[],[f13])).
% 0.15/0.45  fof(f13,plain,(
% 0.15/0.45    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.15/0.45    inference(flattening,[],[f12])).
% 0.15/0.45  fof(f12,plain,(
% 0.15/0.45    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.15/0.45    inference(ennf_transformation,[],[f3])).
% 0.15/0.45  fof(f3,axiom,(
% 0.15/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.15/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.15/0.45  fof(f52,plain,(
% 0.15/0.45    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.15/0.45    inference(forward_demodulation,[],[f51,f42])).
% 0.15/0.45  fof(f51,plain,(
% 0.15/0.45    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.15/0.45    inference(forward_demodulation,[],[f27,f42])).
% 0.15/0.45  fof(f27,plain,(
% 0.15/0.45    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.15/0.45    inference(cnf_transformation,[],[f21])).
% 0.15/0.45  fof(f93,plain,(
% 0.15/0.45    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.15/0.45    inference(subsumption_resolution,[],[f91,f37])).
% 0.15/0.45  fof(f91,plain,(
% 0.15/0.45    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.15/0.45    inference(resolution,[],[f90,f24])).
% 0.15/0.45  fof(f90,plain,(
% 0.15/0.45    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(X0)) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))) )),
% 0.15/0.45    inference(subsumption_resolution,[],[f89,f24])).
% 0.15/0.45  fof(f89,plain,(
% 0.15/0.45    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) | ~v1_relat_1(sK0)) )),
% 0.15/0.45    inference(resolution,[],[f58,f28])).
% 0.15/0.45  fof(f58,plain,(
% 0.15/0.45    ( ! [X0] : (~v1_relat_1(k4_relat_1(sK0)) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))) )),
% 0.15/0.45    inference(forward_demodulation,[],[f56,f50])).
% 0.15/0.45  fof(f50,plain,(
% 0.15/0.45    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.15/0.45    inference(forward_demodulation,[],[f49,f42])).
% 0.15/0.45  fof(f49,plain,(
% 0.15/0.45    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.15/0.45    inference(subsumption_resolution,[],[f48,f24])).
% 0.15/0.45  fof(f48,plain,(
% 0.15/0.45    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.15/0.45    inference(subsumption_resolution,[],[f47,f25])).
% 0.15/0.45  fof(f47,plain,(
% 0.15/0.45    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.15/0.45    inference(resolution,[],[f33,f26])).
% 0.15/0.45  fof(f33,plain,(
% 0.15/0.45    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.15/0.45    inference(cnf_transformation,[],[f19])).
% 0.15/0.45  fof(f56,plain,(
% 0.15/0.45    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X0)) | k2_relat_1(k4_relat_1(sK0)) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) | ~v1_relat_1(X0) | ~v1_relat_1(k4_relat_1(sK0))) )),
% 0.15/0.45    inference(superposition,[],[f30,f46])).
% 0.15/0.45  fof(f30,plain,(
% 0.15/0.45    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.15/0.45    inference(cnf_transformation,[],[f15])).
% 0.15/0.45  fof(f15,plain,(
% 0.15/0.45    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.15/0.45    inference(flattening,[],[f14])).
% 0.15/0.45  fof(f14,plain,(
% 0.15/0.45    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.15/0.45    inference(ennf_transformation,[],[f4])).
% 0.15/0.45  fof(f4,axiom,(
% 0.15/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.15/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.15/0.45  % SZS output end Proof for theBenchmark
% 0.15/0.45  % (22727)------------------------------
% 0.15/0.45  % (22727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.45  % (22727)Termination reason: Refutation
% 0.15/0.45  
% 0.15/0.45  % (22727)Memory used [KB]: 6140
% 0.15/0.45  % (22727)Time elapsed: 0.073 s
% 0.15/0.45  % (22727)------------------------------
% 0.15/0.45  % (22727)------------------------------
% 0.15/0.45  % (22705)Success in time 0.131 s
%------------------------------------------------------------------------------
