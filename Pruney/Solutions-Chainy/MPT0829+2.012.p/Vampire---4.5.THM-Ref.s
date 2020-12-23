%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 129 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   17
%              Number of atoms          :  147 ( 411 expanded)
%              Number of equality atoms :   29 (  90 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f117,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).

fof(f21,plain,
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

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

fof(f117,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f116,f71])).

fof(f71,plain,(
    r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f51,f57])).

fof(f57,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f51,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f50,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f48,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f27,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f27,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f114,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f114,plain,(
    ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f28,f107])).

fof(f107,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f55,f97])).

fof(f97,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f93,f81])).

fof(f81,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f53,f57])).

fof(f53,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f52,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f49,f29])).

fof(f49,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f91,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f89,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f88,f26])).

fof(f88,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f54,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f26,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f55,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f26,f41])).

fof(f28,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (6028)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (6036)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (6031)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (6034)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (6036)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f117,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f116,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    r1_tarski(sK1,k1_relat_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f51,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f26,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f50,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f48,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.52    inference(resolution,[],[f27,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ~r1_tarski(sK1,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(superposition,[],[f114,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    sK1 != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.52    inference(backward_demodulation,[],[f28,f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f55,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f93,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f53,f57])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f52,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f49,f29])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.52    inference(resolution,[],[f27,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f91,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.52    inference(resolution,[],[f89,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f88,f26])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(superposition,[],[f54,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.22/0.52    inference(resolution,[],[f26,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f26,f41])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (6036)------------------------------
% 0.22/0.52  % (6036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6036)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (6036)Memory used [KB]: 1663
% 0.22/0.52  % (6036)Time elapsed: 0.096 s
% 0.22/0.52  % (6036)------------------------------
% 0.22/0.52  % (6036)------------------------------
% 0.22/0.52  % (6027)Success in time 0.157 s
%------------------------------------------------------------------------------
