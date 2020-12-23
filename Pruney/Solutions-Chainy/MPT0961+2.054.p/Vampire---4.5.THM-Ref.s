%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 577 expanded)
%              Number of leaves         :    6 ( 117 expanded)
%              Depth                    :   21
%              Number of atoms          :  158 (1972 expanded)
%              Number of equality atoms :   52 ( 346 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f96,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f96,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_xboole_0,X1)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(backward_demodulation,[],[f57,f71])).

fof(f71,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f70,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f70,plain,
    ( ~ v1_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(superposition,[],[f19,f55])).

fof(f55,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f54,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f53,f47])).

fof(f47,plain,(
    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | k1_relat_1(sK0) = k1_relset_1(X0,k2_relat_1(sK0),sK0) ) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X1)
      | k1_relat_1(sK0) = k1_relset_1(X1,X0,sK0) ) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(sK0),X1)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f24,f17])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f53,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,(
    ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f44,f32])).

fof(f44,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f42,f32])).

fof(f42,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f16,f18])).

fof(f18,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_2(sK0,X0,k2_relat_1(sK0))
      | k1_relset_1(X0,k2_relat_1(sK0),sK0) != X0
      | k1_xboole_0 = k2_relat_1(sK0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | k1_relset_1(X1,X0,sK0) != X1
      | v1_funct_2(sK0,X1,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(k1_relat_1(sK0),X1) ) ),
    inference(resolution,[],[f30,f41])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(backward_demodulation,[],[f41,f55])).

fof(f94,plain,(
    ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f93,f74])).

fof(f74,plain,(
    ~ v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f59,f71])).

fof(f59,plain,(
    ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f55])).

fof(f93,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f35,f76])).

fof(f76,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f61,f71])).

fof(f61,plain,(
    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f47,f55])).

fof(f35,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (4827)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.47  % (4827)Refutation not found, incomplete strategy% (4827)------------------------------
% 0.20/0.47  % (4827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4841)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.48  % (4827)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (4827)Memory used [KB]: 6012
% 0.20/0.48  % (4827)Time elapsed: 0.075 s
% 0.20/0.48  % (4827)------------------------------
% 0.20/0.48  % (4827)------------------------------
% 0.20/0.49  % (4832)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (4841)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f96,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    inference(resolution,[],[f94,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_xboole_0,X1) | ~r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f57,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f70,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    v1_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ~v1_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.49    inference(superposition,[],[f19,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f54,f32])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f53,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.20/0.49    inference(resolution,[],[f46,f32])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | k1_relat_1(sK0) = k1_relset_1(X0,k2_relat_1(sK0),sK0)) )),
% 0.20/0.49    inference(resolution,[],[f43,f32])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X1) | k1_relat_1(sK0) = k1_relset_1(X1,X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f41,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(sK0),X1) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.20/0.49    inference(resolution,[],[f24,f17])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.20/0.49    inference(resolution,[],[f52,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f44,f32])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f42,f32])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.49    inference(resolution,[],[f41,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f16,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    v1_funct_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ~v1_funct_1(sK0) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_2(sK0,X0,k2_relat_1(sK0)) | k1_relset_1(X0,k2_relat_1(sK0),sK0) != X0 | k1_xboole_0 = k2_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.20/0.49    inference(resolution,[],[f50,f32])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK0),X0) | k1_relset_1(X1,X0,sK0) != X1 | v1_funct_2(sK0,X1,X0) | k1_xboole_0 = X0 | ~r1_tarski(k1_relat_1(sK0),X1)) )),
% 0.20/0.49    inference(resolution,[],[f30,f41])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f41,f55])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f93,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    inference(backward_demodulation,[],[f59,f71])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.20/0.49    inference(backward_demodulation,[],[f45,f55])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    inference(superposition,[],[f35,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f61,f71])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f47,f55])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (4841)------------------------------
% 0.20/0.49  % (4841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4841)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (4841)Memory used [KB]: 1663
% 0.20/0.49  % (4841)Time elapsed: 0.093 s
% 0.20/0.49  % (4841)------------------------------
% 0.20/0.49  % (4841)------------------------------
% 0.20/0.49  % (4818)Success in time 0.135 s
%------------------------------------------------------------------------------
