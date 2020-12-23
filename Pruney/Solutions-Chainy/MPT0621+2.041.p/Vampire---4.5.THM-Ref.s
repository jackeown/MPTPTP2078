%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 271 expanded)
%              Number of leaves         :    6 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  141 (1449 expanded)
%              Number of equality atoms :   76 ( 684 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3953)Termination reason: Refutation not found, incomplete strategy

% (3953)Memory used [KB]: 10490
% (3953)Time elapsed: 0.073 s
% (3953)------------------------------
% (3953)------------------------------
fof(f105,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73,f50])).

fof(f50,plain,(
    ! [X2,X1] : X1 = X2 ),
    inference(superposition,[],[f45,f45])).

fof(f45,plain,(
    ! [X4,X5] : k1_funct_1(sK2(sK0,X5),sK1(sK0)) = X4 ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f9])).

fof(f9,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f36,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK2(sK0,X5),sK1(sK0)) = X4
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] : sK2(sK0,X0) = sK2(sK0,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X1
      | sK2(X1,X2) = sK2(sK0,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != X0
      | sK2(X0,X1) = sK2(X2,X3)
      | sK0 != X2 ) ),
    inference(superposition,[],[f27,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK2(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK2(X0,X1)) = X0
      & v1_funct_1(sK2(X0,X1))
      & v1_relat_1(sK2(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK2(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != k1_relat_1(sK2(X0,X1))
      | sK2(X0,X1) = sK2(X2,X3)
      | sK0 != X2 ) ),
    inference(subsumption_resolution,[],[f26,f18])).

fof(f18,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != k1_relat_1(sK2(X0,X1))
      | sK2(X0,X1) = sK2(X2,X3)
      | sK0 != X2
      | ~ v1_relat_1(sK2(X0,X1)) ) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | sK2(X0,X1) = X2
      | sK0 != X0
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f23,f20])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( sK0 != k1_relat_1(sK2(X0,X1))
      | k1_relat_1(X2) != sK0
      | sK2(X0,X1) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( sK0 != k1_relat_1(sK2(X0,X1))
      | k1_relat_1(X2) != sK0
      | sK2(X0,X1) = X2
      | ~ v1_relat_1(sK2(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f15,f19])).

fof(f15,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | X1 = X2
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2(X0,X1),sK1(X0)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f21,f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f11])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK2(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 != X0 ),
    inference(superposition,[],[f16,f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (3946)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (3950)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (3952)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (3954)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (3953)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (3952)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (3953)Refutation not found, incomplete strategy% (3953)------------------------------
% 0.21/0.49  % (3953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (3953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3953)Memory used [KB]: 10490
% 0.21/0.49  % (3953)Time elapsed: 0.073 s
% 0.21/0.49  % (3953)------------------------------
% 0.21/0.49  % (3953)------------------------------
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f73,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X1] : (X1 = X2) )),
% 0.21/0.49    inference(superposition,[],[f45,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k1_funct_1(sK2(sK0,X5),sK1(sK0)) = X4) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f36,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(flattening,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k1_funct_1(sK2(sK0,X5),sK1(sK0)) = X4 | k1_xboole_0 = sK0) )),
% 0.21/0.49    inference(superposition,[],[f25,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sK2(sK0,X0) = sK2(sK0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sK0 != X1 | sK2(X1,X2) = sK2(sK0,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sK0 != X0 | sK2(X0,X1) = sK2(X2,X3) | sK0 != X2) )),
% 0.21/0.49    inference(superposition,[],[f27,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sK0 != k1_relat_1(sK2(X0,X1)) | sK2(X0,X1) = sK2(X2,X3) | sK0 != X2) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f26,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sK0 != k1_relat_1(sK2(X0,X1)) | sK2(X0,X1) = sK2(X2,X3) | sK0 != X2 | ~v1_relat_1(sK2(X0,X1))) )),
% 0.21/0.49    inference(resolution,[],[f24,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | sK2(X0,X1) = X2 | sK0 != X0 | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f23,f20])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sK0 != k1_relat_1(sK2(X0,X1)) | k1_relat_1(X2) != sK0 | sK2(X0,X1) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f22,f18])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sK0 != k1_relat_1(sK2(X0,X1)) | k1_relat_1(X2) != sK0 | sK2(X0,X1) = X2 | ~v1_relat_1(sK2(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(resolution,[],[f15,f19])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | X1 = X2 | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_funct_1(sK2(X0,X1),sK1(X0)) = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(resolution,[],[f21,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK2(X0,X1),X3) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != X0) )),
% 0.21/0.49    inference(superposition,[],[f16,f50])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3952)------------------------------
% 0.21/0.49  % (3952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3952)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3952)Memory used [KB]: 10618
% 0.21/0.49  % (3952)Time elapsed: 0.072 s
% 0.21/0.49  % (3952)------------------------------
% 0.21/0.49  % (3952)------------------------------
% 0.21/0.49  % (3941)Success in time 0.125 s
%------------------------------------------------------------------------------
