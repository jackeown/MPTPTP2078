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
% DateTime   : Thu Dec  3 12:56:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  47 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 161 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(global_subsumption,[],[f38,f52])).

fof(f52,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f23,f27,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
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

fof(f27,plain,(
    ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f18,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f18,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X0,X1) )
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(f23,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f15,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f16,f17,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f17,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (18107)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (18116)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.49  % (18100)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (18116)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f38,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f23,f27,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~r1_tarski(sK4,k2_zfmisc_1(sK1,sK3))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f18,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    r1_tarski(sK4,k2_zfmisc_1(sK0,sK2))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f15,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f16,f17,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18116)------------------------------
% 0.21/0.49  % (18116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18116)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18116)Memory used [KB]: 5373
% 0.21/0.49  % (18116)Time elapsed: 0.079 s
% 0.21/0.49  % (18116)------------------------------
% 0.21/0.49  % (18116)------------------------------
% 0.21/0.49  % (18094)Success in time 0.134 s
%------------------------------------------------------------------------------
