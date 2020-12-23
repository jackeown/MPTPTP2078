%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  65 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 323 expanded)
%              Number of equality atoms :   31 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f15])).

fof(f15,plain,(
    k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1))
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8,f7])).

fof(f7,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
                & k1_relat_1(X1) = k1_relat_1(X0)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(k5_relat_1(X2,sK0))
              & k1_relat_1(X1) = k1_relat_1(sK0)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(k5_relat_1(X2,sK0))
            & k1_relat_1(X1) = k1_relat_1(sK0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_relat_1(k5_relat_1(X2,sK0)) != k1_relat_1(k5_relat_1(X2,sK1))
          & k1_relat_1(sK0) = k1_relat_1(sK1)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X2] :
        ( k1_relat_1(k5_relat_1(X2,sK0)) != k1_relat_1(k5_relat_1(X2,sK1))
        & k1_relat_1(sK0) = k1_relat_1(sK1)
        & v1_relat_1(X2) )
   => ( k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1))
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
              & k1_relat_1(X1) = k1_relat_1(X0)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
              & k1_relat_1(X1) = k1_relat_1(X0)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k1_relat_1(X1) = k1_relat_1(X0)
                 => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X1) = k1_relat_1(X0)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f32,plain,(
    k1_relat_1(k5_relat_1(sK2,sK0)) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f29,f19])).

fof(f19,plain,(
    k1_relat_1(k5_relat_1(sK2,sK0)) = k10_relat_1(sK2,k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f13,f11,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f22,f14])).

fof(f14,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f13,f12,f16])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (9003)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (9009)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (9005)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (9003)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f32,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ((k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1)) & k1_relat_1(sK0) = k1_relat_1(sK1) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8,f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1)) & k1_relat_1(X1) = k1_relat_1(X0) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(k5_relat_1(X2,sK0)) & k1_relat_1(X1) = k1_relat_1(sK0) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(k5_relat_1(X2,sK0)) & k1_relat_1(X1) = k1_relat_1(sK0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k1_relat_1(k5_relat_1(X2,sK0)) != k1_relat_1(k5_relat_1(X2,sK1)) & k1_relat_1(sK0) = k1_relat_1(sK1) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X2] : (k1_relat_1(k5_relat_1(X2,sK0)) != k1_relat_1(k5_relat_1(X2,sK1)) & k1_relat_1(sK0) = k1_relat_1(sK1) & v1_relat_1(X2)) => (k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1)) & k1_relat_1(sK0) = k1_relat_1(sK1) & v1_relat_1(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1)) & k1_relat_1(X1) = k1_relat_1(X0) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f4])).
% 0.21/0.43  fof(f4,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X1) = k1_relat_1(X0) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f2])).
% 0.21/0.43  fof(f2,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X1) = k1_relat_1(X0) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    k1_relat_1(k5_relat_1(sK2,sK0)) = k1_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.43    inference(backward_demodulation,[],[f29,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    k1_relat_1(k5_relat_1(sK2,sK0)) = k10_relat_1(sK2,k1_relat_1(sK0))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f13,f11,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    v1_relat_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK0))),
% 0.21/0.43    inference(forward_demodulation,[],[f22,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f13,f12,f16])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (9003)------------------------------
% 0.21/0.43  % (9003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (9003)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (9003)Memory used [KB]: 6012
% 0.21/0.43  % (9003)Time elapsed: 0.004 s
% 0.21/0.43  % (9003)------------------------------
% 0.21/0.43  % (9003)------------------------------
% 0.21/0.43  % (9000)Success in time 0.073 s
%------------------------------------------------------------------------------
