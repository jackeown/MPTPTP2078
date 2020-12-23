%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 133 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  158 ( 418 expanded)
%              Number of equality atoms :   37 ( 104 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f83])).

fof(f83,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f82,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

fof(f82,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f81,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f81,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f34,f80])).

fof(f80,plain,(
    r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f79,f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK1,k1_relset_1(X0,X1,sK2)) ) ),
    inference(resolution,[],[f47,f33])).

fof(f33,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f34,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f96,f36])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f96,plain,(
    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f36,f94])).

fof(f94,plain,(
    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(resolution,[],[f92,f32])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f90,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f75,f89])).

fof(f89,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f88,f32])).

fof(f88,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f86,f45])).

fof(f86,plain,(
    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f85,f32])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK1,k2_relset_1(X0,X1,sK2)) ) ),
    inference(resolution,[],[f48,f33])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f54,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f72,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k6_relat_1(X2) = k6_relat_1(X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f71,f36])).

fof(f71,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X2) = k6_relat_1(X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X3)),X2) ) ),
    inference(subsumption_resolution,[],[f69,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f69,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X2) = k6_relat_1(X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X3)),X2)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f68,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f66,f37])).

fof(f37,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f41,f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:38:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (29960)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.46  % (29943)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.46  % (29943)Refutation not found, incomplete strategy% (29943)------------------------------
% 0.19/0.46  % (29943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (29943)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (29943)Memory used [KB]: 10618
% 0.19/0.46  % (29943)Time elapsed: 0.071 s
% 0.19/0.46  % (29943)------------------------------
% 0.19/0.46  % (29943)------------------------------
% 0.19/0.46  % (29953)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.46  % (29960)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f108,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(subsumption_resolution,[],[f107,f83])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    sK1 != k2_relat_1(sK2)),
% 0.19/0.46    inference(subsumption_resolution,[],[f82,f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.46    inference(cnf_transformation,[],[f30])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(flattening,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.19/0.46    inference(negated_conjecture,[],[f11])).
% 0.19/0.46  fof(f11,conjecture,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.46    inference(superposition,[],[f81,f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f9])).
% 0.19/0.46  fof(f9,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.46  fof(f81,plain,(
% 0.19/0.46    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.19/0.46    inference(subsumption_resolution,[],[f34,f80])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.19/0.46    inference(resolution,[],[f79,f32])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK1,k1_relset_1(X0,X1,sK2))) )),
% 0.19/0.46    inference(resolution,[],[f47,f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f30])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(flattening,[],[f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f30])).
% 0.19/0.46  fof(f107,plain,(
% 0.19/0.46    sK1 = k2_relat_1(sK2)),
% 0.19/0.46    inference(forward_demodulation,[],[f96,f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))),
% 0.19/0.46    inference(superposition,[],[f36,f94])).
% 0.19/0.46  fof(f94,plain,(
% 0.19/0.46    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 0.19/0.46    inference(resolution,[],[f92,f32])).
% 0.19/0.46  fof(f92,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))) )),
% 0.19/0.46    inference(resolution,[],[f90,f44])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.46  fof(f90,plain,(
% 0.19/0.46    ~v1_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 0.19/0.46    inference(subsumption_resolution,[],[f75,f89])).
% 0.19/0.46  fof(f89,plain,(
% 0.19/0.46    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.19/0.46    inference(subsumption_resolution,[],[f88,f32])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    r1_tarski(sK1,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.46    inference(superposition,[],[f86,f45])).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 0.19/0.46    inference(resolution,[],[f85,f32])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK1,k2_relset_1(X0,X1,sK2))) )),
% 0.19/0.46    inference(resolution,[],[f48,f33])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    ~r1_tarski(sK1,k2_relat_1(sK2)) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f72,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 0.19/0.47    inference(resolution,[],[f54,f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    v5_relat_1(sK2,sK1)),
% 0.19/0.47    inference(resolution,[],[f46,f32])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k6_relat_1(X2) = k6_relat_1(X3) | ~r1_tarski(X2,X3)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f71,f36])).
% 0.19/0.47  fof(f71,plain,(
% 0.19/0.47    ( ! [X2,X3] : (k6_relat_1(X2) = k6_relat_1(X3) | ~r1_tarski(X2,X3) | ~r1_tarski(k1_relat_1(k6_relat_1(X3)),X2)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f69,f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    ( ! [X2,X3] : (k6_relat_1(X2) = k6_relat_1(X3) | ~r1_tarski(X2,X3) | ~r1_tarski(k1_relat_1(k6_relat_1(X3)),X2) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.19/0.47    inference(superposition,[],[f68,f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f66,f37])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f3])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.19/0.47    inference(resolution,[],[f41,f35])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (29960)------------------------------
% 0.19/0.47  % (29960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (29960)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (29960)Memory used [KB]: 6140
% 0.19/0.47  % (29960)Time elapsed: 0.077 s
% 0.19/0.47  % (29960)------------------------------
% 0.19/0.47  % (29960)------------------------------
% 0.19/0.47  % (29937)Success in time 0.118 s
%------------------------------------------------------------------------------
