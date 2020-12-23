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
% DateTime   : Thu Dec  3 12:54:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  51 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 196 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73,f18])).

fof(f18,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
    & r1_tarski(k9_relat_1(sK2,sK0),sK1)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
        & r1_tarski(k9_relat_1(X2,X0),X1)
        & r1_tarski(X0,k1_relat_1(X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
      & r1_tarski(k9_relat_1(sK2,sK0),sK1)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f73,plain,(
    ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f72,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f68,f20])).

fof(f20,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f47,f19])).

fof(f19,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X0,X1),X2)
      | r1_tarski(X1,k10_relat_1(X0,X2))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X1,k10_relat_1(X0,X2))
      | ~ r1_tarski(k9_relat_1(X0,X1),X2)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f41,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f41,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X6,k10_relat_1(X5,X3))
      | ~ v1_relat_1(X5)
      | r1_tarski(X6,k10_relat_1(X5,X4))
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f22,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.41  % (23975)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.42  % (23975)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(subsumption_resolution,[],[f73,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_relat_1(sK2)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_relat_1(X2)) => (~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_relat_1(sK2))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_relat_1(X2))),
% 0.22/0.42    inference(flattening,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0,X1,X2] : ((~r1_tarski(X0,k10_relat_1(X2,X1)) & (r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)))) & v1_relat_1(X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.22/0.42    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    ~r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.42    inference(subsumption_resolution,[],[f72,f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    v1_relat_1(sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    ~v1_relat_1(sK2) | ~r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.42    inference(subsumption_resolution,[],[f68,f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ~r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    r1_tarski(sK0,k10_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.42    inference(resolution,[],[f47,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X0,X1),X2) | r1_tarski(X1,k10_relat_1(X0,X2)) | ~v1_relat_1(X0) | ~r1_tarski(X1,k1_relat_1(X0))) )),
% 0.22/0.42    inference(duplicate_literal_removal,[],[f44])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(X1,k10_relat_1(X0,X2)) | ~r1_tarski(k9_relat_1(X0,X1),X2) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(resolution,[],[f41,f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(flattening,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    ( ! [X6,X4,X5,X3] : (~r1_tarski(X6,k10_relat_1(X5,X3)) | ~v1_relat_1(X5) | r1_tarski(X6,k10_relat_1(X5,X4)) | ~r1_tarski(X3,X4)) )),
% 0.22/0.42    inference(resolution,[],[f22,f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.42    inference(flattening,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (23975)------------------------------
% 0.22/0.42  % (23975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (23975)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (23975)Memory used [KB]: 5373
% 0.22/0.42  % (23975)Time elapsed: 0.006 s
% 0.22/0.42  % (23975)------------------------------
% 0.22/0.42  % (23975)------------------------------
% 0.22/0.42  % (23967)Success in time 0.061 s
%------------------------------------------------------------------------------
