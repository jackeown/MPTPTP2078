%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:06 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   36 (  67 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 301 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(global_subsumption,[],[f23,f22,f20,f40])).

fof(f40,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    sK2 = k8_relat_1(sK0,sK2) ),
    inference(global_subsumption,[],[f20,f35])).

fof(f35,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f34,f21])).

fof(f21,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
    & r2_hidden(sK1,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
        & r2_hidden(X1,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
   => ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
      & r2_hidden(sK1,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f39,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k8_relat_1(sK0,sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f30,f32])).

fof(f32,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK1),sK0) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:52:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.42  % (25590)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.15/0.42  % (25590)Refutation found. Thanks to Tanya!
% 0.15/0.42  % SZS status Theorem for theBenchmark
% 0.15/0.42  % SZS output start Proof for theBenchmark
% 0.15/0.42  fof(f41,plain,(
% 0.15/0.42    $false),
% 0.15/0.42    inference(global_subsumption,[],[f23,f22,f20,f40])).
% 0.15/0.42  fof(f40,plain,(
% 0.15/0.42    ~r2_hidden(sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.15/0.42    inference(forward_demodulation,[],[f39,f38])).
% 0.15/0.42  fof(f38,plain,(
% 0.15/0.42    sK2 = k8_relat_1(sK0,sK2)),
% 0.15/0.42    inference(global_subsumption,[],[f20,f35])).
% 0.15/0.42  fof(f35,plain,(
% 0.15/0.42    ~v1_relat_1(sK2) | sK2 = k8_relat_1(sK0,sK2)),
% 0.15/0.42    inference(resolution,[],[f34,f21])).
% 0.15/0.42  fof(f21,plain,(
% 0.15/0.42    v5_relat_1(sK2,sK0)),
% 0.15/0.42    inference(cnf_transformation,[],[f16])).
% 0.15/0.42  fof(f16,plain,(
% 0.15/0.42    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0) & r2_hidden(sK1,k1_relat_1(sK2)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)),
% 0.15/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15])).
% 0.15/0.42  fof(f15,plain,(
% 0.15/0.42    ? [X0,X1,X2] : (~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (~m1_subset_1(k1_funct_1(sK2,sK1),sK0) & r2_hidden(sK1,k1_relat_1(sK2)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.15/0.42    introduced(choice_axiom,[])).
% 0.15/0.42  fof(f8,plain,(
% 0.15/0.42    ? [X0,X1,X2] : (~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))),
% 0.15/0.42    inference(flattening,[],[f7])).
% 0.15/0.42  fof(f7,plain,(
% 0.15/0.42    ? [X0,X1,X2] : ((~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2))) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)))),
% 0.15/0.42    inference(ennf_transformation,[],[f6])).
% 0.15/0.42  fof(f6,negated_conjecture,(
% 0.15/0.42    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.15/0.42    inference(negated_conjecture,[],[f5])).
% 0.15/0.42  fof(f5,conjecture,(
% 0.15/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 0.15/0.42  fof(f34,plain,(
% 0.15/0.42    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.15/0.42    inference(duplicate_literal_removal,[],[f33])).
% 0.15/0.42  fof(f33,plain,(
% 0.15/0.42    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.15/0.42    inference(resolution,[],[f25,f26])).
% 0.15/0.42  fof(f26,plain,(
% 0.15/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.15/0.42    inference(cnf_transformation,[],[f17])).
% 0.15/0.42  fof(f17,plain,(
% 0.15/0.42    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.15/0.42    inference(nnf_transformation,[],[f11])).
% 0.15/0.42  fof(f11,plain,(
% 0.15/0.42    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.15/0.42    inference(ennf_transformation,[],[f2])).
% 0.15/0.42  fof(f2,axiom,(
% 0.15/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.15/0.42  fof(f25,plain,(
% 0.15/0.42    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.15/0.42    inference(cnf_transformation,[],[f10])).
% 0.15/0.42  fof(f10,plain,(
% 0.15/0.42    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.15/0.42    inference(flattening,[],[f9])).
% 0.15/0.42  fof(f9,plain,(
% 0.15/0.42    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.15/0.42    inference(ennf_transformation,[],[f3])).
% 0.15/0.42  fof(f3,axiom,(
% 0.15/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.15/0.42  fof(f39,plain,(
% 0.15/0.42    ~r2_hidden(sK1,k1_relat_1(k8_relat_1(sK0,sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.15/0.42    inference(resolution,[],[f30,f32])).
% 0.15/0.42  fof(f32,plain,(
% 0.15/0.42    ~r2_hidden(k1_funct_1(sK2,sK1),sK0)),
% 0.15/0.42    inference(resolution,[],[f28,f24])).
% 0.15/0.42  fof(f24,plain,(
% 0.15/0.42    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0)),
% 0.15/0.42    inference(cnf_transformation,[],[f16])).
% 0.15/0.42  fof(f28,plain,(
% 0.15/0.42    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.15/0.42    inference(cnf_transformation,[],[f12])).
% 0.15/0.42  fof(f12,plain,(
% 0.15/0.42    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.15/0.42    inference(ennf_transformation,[],[f1])).
% 0.15/0.42  fof(f1,axiom,(
% 0.15/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.15/0.42  fof(f30,plain,(
% 0.15/0.42    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.15/0.42    inference(cnf_transformation,[],[f19])).
% 0.15/0.42  fof(f19,plain,(
% 0.15/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.15/0.42    inference(flattening,[],[f18])).
% 0.15/0.42  fof(f18,plain,(
% 0.15/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.15/0.42    inference(nnf_transformation,[],[f14])).
% 0.15/0.42  fof(f14,plain,(
% 0.15/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.15/0.42    inference(flattening,[],[f13])).
% 0.15/0.42  fof(f13,plain,(
% 0.15/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.15/0.42    inference(ennf_transformation,[],[f4])).
% 0.15/0.42  fof(f4,axiom,(
% 0.15/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).
% 0.15/0.42  fof(f20,plain,(
% 0.15/0.42    v1_relat_1(sK2)),
% 0.15/0.42    inference(cnf_transformation,[],[f16])).
% 0.15/0.42  fof(f22,plain,(
% 0.15/0.42    v1_funct_1(sK2)),
% 0.15/0.42    inference(cnf_transformation,[],[f16])).
% 0.15/0.43  fof(f23,plain,(
% 0.15/0.43    r2_hidden(sK1,k1_relat_1(sK2))),
% 0.15/0.43    inference(cnf_transformation,[],[f16])).
% 0.15/0.43  % SZS output end Proof for theBenchmark
% 0.15/0.43  % (25590)------------------------------
% 0.15/0.43  % (25590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.43  % (25590)Termination reason: Refutation
% 0.15/0.43  
% 0.15/0.43  % (25590)Memory used [KB]: 6140
% 0.15/0.43  % (25590)Time elapsed: 0.005 s
% 0.15/0.43  % (25590)------------------------------
% 0.15/0.43  % (25590)------------------------------
% 0.22/0.43  % (25585)Success in time 0.062 s
%------------------------------------------------------------------------------
