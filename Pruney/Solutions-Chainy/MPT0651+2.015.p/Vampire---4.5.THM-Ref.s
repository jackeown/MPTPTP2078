%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 185 expanded)
%              Number of leaves         :    9 (  45 expanded)
%              Depth                    :   31
%              Number of atoms          :  199 ( 798 expanded)
%              Number of equality atoms :   57 ( 282 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(subsumption_resolution,[],[f69,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f22])).

fof(f22,plain,
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

fof(f12,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f69,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f68,f25])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f67,f26])).

fof(f26,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f65,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f65,plain,(
    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f64,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f29,f28])).

fof(f28,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f64,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f63,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f62,f24])).

fof(f62,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f61,f25])).

fof(f61,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f60,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f58,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f24])).

fof(f57,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f56,f25])).

fof(f56,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f55,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f55,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f54,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(superposition,[],[f53,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f53,plain,(
    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(subsumption_resolution,[],[f27,f52])).

fof(f52,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(subsumption_resolution,[],[f51,f37])).

fof(f51,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f50,f36])).

fof(f50,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(subsumption_resolution,[],[f49,f24])).

fof(f49,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f48,f25])).

fof(f48,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f47,f26])).

fof(f47,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f44,f34])).

fof(f44,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0)))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(resolution,[],[f42,f24])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(k2_funct_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f40,f24])).

fof(f40,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(k2_funct_1(sK0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f39,f25])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,k2_funct_1(X2)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f27,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:22:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (2003)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.48  % (1992)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.49  % (2011)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.49  % (1999)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (2011)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ~v1_relat_1(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    v1_funct_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f67,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v2_funct_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    k1_relat_1(sK0) != k1_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(superposition,[],[f65,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f64,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f29,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0)))),
% 0.22/0.49    inference(resolution,[],[f63,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f62,f24])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f61,f25])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f60,f26])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(superposition,[],[f58,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ~r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f57,f24])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f56,f25])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(resolution,[],[f55,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~v1_relat_1(k2_funct_1(sK0)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f54,f24])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.49    inference(superposition,[],[f53,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f27,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f51,f37])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0)))),
% 0.22/0.49    inference(resolution,[],[f50,f36])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f49,f24])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f48,f25])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f47,f26])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(superposition,[],[f44,f34])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.49    inference(resolution,[],[f42,f24])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(k2_funct_1(sK0)))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f40,f24])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(sK0)) )),
% 0.22/0.49    inference(resolution,[],[f39,f25])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,k2_funct_1(X2))) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X2))) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(resolution,[],[f30,f32])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (2011)------------------------------
% 0.22/0.49  % (2011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (2011)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (2011)Memory used [KB]: 6140
% 0.22/0.49  % (2011)Time elapsed: 0.074 s
% 0.22/0.49  % (2011)------------------------------
% 0.22/0.49  % (2011)------------------------------
% 0.22/0.49  % (1991)Success in time 0.133 s
%------------------------------------------------------------------------------
