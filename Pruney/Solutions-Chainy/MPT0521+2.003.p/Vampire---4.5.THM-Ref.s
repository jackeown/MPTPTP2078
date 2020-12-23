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
% DateTime   : Thu Dec  3 12:48:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  42 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 120 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_relat_1)).

fof(f37,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f36,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f36,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f35,f21])).

fof(f21,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
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

fof(f35,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f34,f24])).

fof(f24,plain,(
    ! [X1] : r1_tarski(k8_relat_1(X1,sK1),sK1) ),
    inference(resolution,[],[f17,f14])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f34,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f33,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f32,f14])).

fof(f32,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f30])).

fof(f30,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f15,f13])).

fof(f13,plain,(
    ~ r1_tarski(k5_relat_1(k8_relat_1(sK0,sK1),sK2),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.46  % (4871)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.46  % (4871)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (4863)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f37,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2))))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_relat_1)).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~v1_relat_1(sK1)),
% 0.20/0.46    inference(resolution,[],[f36,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.46    inference(subsumption_resolution,[],[f35,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.46    inference(equality_resolution,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ~r1_tarski(sK2,sK2) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.46    inference(subsumption_resolution,[],[f34,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X1] : (r1_tarski(k8_relat_1(X1,sK1),sK1)) )),
% 0.20/0.46    inference(resolution,[],[f17,f14])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.46    inference(subsumption_resolution,[],[f33,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    v1_relat_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ~v1_relat_1(sK2) | ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.46    inference(subsumption_resolution,[],[f32,f14])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.46    inference(resolution,[],[f15,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ~r1_tarski(k5_relat_1(k8_relat_1(sK0,sK1),sK2),k5_relat_1(sK1,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (4871)------------------------------
% 0.20/0.46  % (4871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4871)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (4871)Memory used [KB]: 1663
% 0.20/0.46  % (4871)Time elapsed: 0.059 s
% 0.20/0.46  % (4871)------------------------------
% 0.20/0.46  % (4871)------------------------------
% 0.20/0.46  % (4851)Success in time 0.107 s
%------------------------------------------------------------------------------
