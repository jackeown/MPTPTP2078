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
% DateTime   : Thu Dec  3 12:53:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  61 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 196 expanded)
%              Number of equality atoms :   22 (  60 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f14])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ v2_funct_1(sK0)
    & ! [X1,X2] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK0)
      & ! [X2,X1] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_funct_1)).

fof(f26,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f25,f15])).

fof(f15,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f24,f17])).

fof(f17,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,
    ( v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f23,f16])).

fof(f16,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,
    ( k9_relat_1(sK0,k6_subset_1(sK1(sK0),k6_subset_1(sK1(sK0),sK2(sK0)))) != k6_subset_1(k9_relat_1(sK0,sK1(sK0)),k9_relat_1(sK0,k6_subset_1(sK1(sK0),sK2(sK0))))
    | v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f22,f16])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k6_subset_1(sK1(X0),k6_subset_1(sK1(X0),sK2(X0)))) != k6_subset_1(k9_relat_1(X0,sK1(X0)),k6_subset_1(k9_relat_1(X0,sK1(X0)),k9_relat_1(X0,sK2(X0))))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f18,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f20,f19,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k9_relat_1(X0,k3_xboole_0(sK1(X0),sK2(X0))) != k3_xboole_0(k9_relat_1(X0,sK1(X0)),k9_relat_1(X0,sK2(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k9_relat_1(X0,k3_xboole_0(sK1(X0),sK2(X0))) != k3_xboole_0(k9_relat_1(X0,sK1(X0)),k9_relat_1(X0,sK2(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
     => k9_relat_1(X0,k3_xboole_0(sK1(X0),sK2(X0))) != k3_xboole_0(k9_relat_1(X0,sK1(X0)),k9_relat_1(X0,sK2(X0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (18327)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.42  % (18327)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(subsumption_resolution,[],[f26,f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    v1_relat_1(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ~v2_funct_1(sK0) & ! [X1,X2] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0] : (~v2_funct_1(X0) & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(sK0) & ! [X2,X1] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0] : (~v2_funct_1(X0) & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.42    inference(flattening,[],[f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ? [X0] : ((~v2_funct_1(X0) & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) => v2_funct_1(X0)))),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) => v2_funct_1(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_funct_1)).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ~v1_relat_1(sK0)),
% 0.22/0.42    inference(subsumption_resolution,[],[f25,f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    v1_funct_1(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.42    inference(subsumption_resolution,[],[f24,f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ~v2_funct_1(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.42    inference(subsumption_resolution,[],[f23,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X2,X1] : (k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    k9_relat_1(sK0,k6_subset_1(sK1(sK0),k6_subset_1(sK1(sK0),sK2(sK0)))) != k6_subset_1(k9_relat_1(sK0,sK1(sK0)),k9_relat_1(sK0,k6_subset_1(sK1(sK0),sK2(sK0)))) | v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.42    inference(superposition,[],[f22,f16])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0] : (k9_relat_1(X0,k6_subset_1(sK1(X0),k6_subset_1(sK1(X0),sK2(X0)))) != k6_subset_1(k9_relat_1(X0,sK1(X0)),k6_subset_1(k9_relat_1(X0,sK1(X0)),k9_relat_1(X0,sK2(X0)))) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f18,f21,f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.22/0.42    inference(definition_unfolding,[],[f20,f19,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0] : (v2_funct_1(X0) | k9_relat_1(X0,k3_xboole_0(sK1(X0),sK2(X0))) != k3_xboole_0(k9_relat_1(X0,sK1(X0)),k9_relat_1(X0,sK2(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0] : (v2_funct_1(X0) | k9_relat_1(X0,k3_xboole_0(sK1(X0),sK2(X0))) != k3_xboole_0(k9_relat_1(X0,sK1(X0)),k9_relat_1(X0,sK2(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0] : (? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) => k9_relat_1(X0,k3_xboole_0(sK1(X0),sK2(X0))) != k3_xboole_0(k9_relat_1(X0,sK1(X0)),k9_relat_1(X0,sK2(X0))))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0] : (v2_funct_1(X0) | ? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(flattening,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0] : ((v2_funct_1(X0) | ? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) => v2_funct_1(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_funct_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (18327)------------------------------
% 0.22/0.42  % (18327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (18327)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (18327)Memory used [KB]: 10490
% 0.22/0.42  % (18327)Time elapsed: 0.004 s
% 0.22/0.42  % (18327)------------------------------
% 0.22/0.42  % (18327)------------------------------
% 0.22/0.42  % (18317)Success in time 0.058 s
%------------------------------------------------------------------------------
