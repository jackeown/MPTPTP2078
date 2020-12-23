%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:49 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 119 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  180 ( 667 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f44])).

fof(f44,plain,(
    r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f23,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).

fof(f59,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f20,f54])).

fof(f54,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f53,f23])).

fof(f53,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = sK2 ),
    inference(resolution,[],[f52,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | sK1 = sK2 ) ),
    inference(subsumption_resolution,[],[f50,f45])).

fof(f45,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f43,f39])).

fof(f39,plain,
    ( v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f38,f21])).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,
    ( ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0)
    | v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f37,f23])).

fof(f37,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0)
    | v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f22,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_partfun1(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | sK1 = sK2 ) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    v1_partfun1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f40,f36])).

fof(f36,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f35,f16])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f34,f18])).

fof(f34,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f17,f27])).

fof(f17,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f18,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK1 = sK2 ) ),
    inference(subsumption_resolution,[],[f32,f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK1,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_funct_1(sK1)
      | sK1 = sK2 ) ),
    inference(subsumption_resolution,[],[f31,f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK1,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_funct_1(sK1)
      | sK1 = sK2 ) ),
    inference(resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_funct_1(X2)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f19,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:10:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.52  % (8663)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.52  % (8646)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.53  % (8646)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f65,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(subsumption_resolution,[],[f59,f44])).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    r2_relset_1(sK0,sK0,sK1,sK1)),
% 0.23/0.53    inference(resolution,[],[f23,f30])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.23/0.53    inference(equality_resolution,[],[f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.53    inference(flattening,[],[f9])).
% 0.23/0.53  fof(f9,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.53    inference(ennf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,plain,(
% 0.23/0.53    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.23/0.53    inference(flattening,[],[f7])).
% 0.23/0.53  fof(f7,plain,(
% 0.23/0.53    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.23/0.53    inference(ennf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.23/0.53    inference(negated_conjecture,[],[f5])).
% 0.23/0.53  fof(f5,conjecture,(
% 0.23/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).
% 0.23/0.53  fof(f59,plain,(
% 0.23/0.53    ~r2_relset_1(sK0,sK0,sK1,sK1)),
% 0.23/0.53    inference(backward_demodulation,[],[f20,f54])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    sK1 = sK2),
% 0.23/0.53    inference(subsumption_resolution,[],[f53,f23])).
% 0.23/0.53  fof(f53,plain,(
% 0.23/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = sK2),
% 0.23/0.53    inference(resolution,[],[f52,f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK1 = sK2) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f50,f45])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    v1_partfun1(sK1,sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f43,f39])).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f38,f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    v1_funct_1(sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    ~v1_funct_1(sK1) | v1_xboole_0(sK0) | v1_partfun1(sK1,sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f37,f23])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | v1_xboole_0(sK0) | v1_partfun1(sK1,sK0)),
% 0.23/0.53    inference(resolution,[],[f22,f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_partfun1(X2,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.23/0.53    inference(flattening,[],[f13])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    v1_funct_2(sK1,sK0,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ~v1_xboole_0(sK0) | v1_partfun1(sK1,sK0)),
% 0.23/0.53    inference(resolution,[],[f23,f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_partfun1(X2,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_partfun1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK1 = sK2) )),
% 0.23/0.53    inference(resolution,[],[f33,f42])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    v1_partfun1(sK2,sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f40,f36])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f35,f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    v1_funct_1(sK2)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ~v1_funct_1(sK2) | v1_xboole_0(sK0) | v1_partfun1(sK2,sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f34,f18])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | v1_xboole_0(sK0) | v1_partfun1(sK2,sK0)),
% 0.23/0.53    inference(resolution,[],[f17,f27])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    v1_funct_2(sK2,sK0,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    ~v1_xboole_0(sK0) | v1_partfun1(sK2,sK0)),
% 0.23/0.53    inference(resolution,[],[f18,f28])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK1 = sK2) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f32,f21])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK1,X0) | ~v1_partfun1(sK2,X0) | ~v1_funct_1(sK1) | sK1 = sK2) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f31,f16])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK1,X0) | ~v1_partfun1(sK2,X0) | ~v1_funct_1(sK1) | sK1 = sK2) )),
% 0.23/0.53    inference(resolution,[],[f19,f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~v1_funct_1(X2) | X2 = X3) )),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.23/0.53    inference(flattening,[],[f11])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.23/0.53    inference(ennf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    r1_partfun1(sK1,sK2)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ~r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (8646)------------------------------
% 0.23/0.53  % (8646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (8646)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (8646)Memory used [KB]: 6140
% 0.23/0.53  % (8646)Time elapsed: 0.069 s
% 0.23/0.53  % (8646)------------------------------
% 0.23/0.53  % (8646)------------------------------
% 0.23/0.53  % (8640)Success in time 0.159 s
%------------------------------------------------------------------------------
