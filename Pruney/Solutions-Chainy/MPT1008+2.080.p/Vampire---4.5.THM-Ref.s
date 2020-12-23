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
% DateTime   : Thu Dec  3 13:04:20 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   39 (  70 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 253 expanded)
%              Number of equality atoms :   60 ( 116 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f46])).

fof(f46,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f21,f43])).

fof(f43,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f19,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f21,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[],[f62,f47])).

fof(f47,plain,(
    k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f40,f44])).

fof(f44,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(resolution,[],[f19,f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f40,plain,(
    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f39,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,
    ( k1_xboole_0 = sK1
    | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f38,f19])).

fof(f38,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | k1_xboole_0 = sK1
    | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(resolution,[],[f18,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f18,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK2)
      | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0)) ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f19,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | k1_tarski(X0) != k1_relat_1(sK2)
      | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0)) ) ),
    inference(resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_tarski(X0)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_relat_1(X1) = k1_tarski(X0)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (19578)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.13/0.41  % (19578)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f67,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(subsumption_resolution,[],[f66,f46])).
% 0.13/0.41  fof(f46,plain,(
% 0.13/0.41    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 0.13/0.41    inference(backward_demodulation,[],[f21,f43])).
% 0.13/0.41  fof(f43,plain,(
% 0.13/0.41    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.13/0.41    inference(resolution,[],[f19,f25])).
% 0.13/0.41  fof(f25,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.41    inference(ennf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.13/0.41    inference(cnf_transformation,[],[f9])).
% 0.13/0.41  fof(f9,plain,(
% 0.13/0.41    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.13/0.41    inference(flattening,[],[f8])).
% 0.13/0.41  fof(f8,plain,(
% 0.13/0.41    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.13/0.41    inference(ennf_transformation,[],[f7])).
% 0.13/0.41  fof(f7,negated_conjecture,(
% 0.13/0.41    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.13/0.41    inference(negated_conjecture,[],[f6])).
% 0.13/0.41  fof(f6,conjecture,(
% 0.13/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.13/0.41    inference(cnf_transformation,[],[f9])).
% 0.13/0.41  fof(f66,plain,(
% 0.13/0.41    k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 0.13/0.41    inference(trivial_inequality_removal,[],[f65])).
% 0.13/0.41  fof(f65,plain,(
% 0.13/0.41    k1_relat_1(sK2) != k1_relat_1(sK2) | k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 0.13/0.41    inference(superposition,[],[f62,f47])).
% 0.13/0.41  fof(f47,plain,(
% 0.13/0.41    k1_tarski(sK0) = k1_relat_1(sK2)),
% 0.13/0.41    inference(backward_demodulation,[],[f40,f44])).
% 0.13/0.41  fof(f44,plain,(
% 0.13/0.41    k1_relat_1(sK2) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 0.13/0.41    inference(resolution,[],[f19,f24])).
% 0.13/0.41  fof(f24,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.41    inference(ennf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.13/0.41  fof(f40,plain,(
% 0.13/0.41    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 0.13/0.41    inference(subsumption_resolution,[],[f39,f20])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    k1_xboole_0 != sK1),
% 0.13/0.41    inference(cnf_transformation,[],[f9])).
% 0.13/0.41  fof(f39,plain,(
% 0.13/0.41    k1_xboole_0 = sK1 | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 0.13/0.41    inference(subsumption_resolution,[],[f38,f19])).
% 0.13/0.41  fof(f38,plain,(
% 0.13/0.41    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | k1_xboole_0 = sK1 | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 0.13/0.41    inference(resolution,[],[f18,f31])).
% 0.13/0.41  fof(f31,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f16])).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.41    inference(flattening,[],[f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.41    inference(ennf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.13/0.41    inference(cnf_transformation,[],[f9])).
% 0.13/0.41  fof(f62,plain,(
% 0.13/0.41    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0))) )),
% 0.13/0.41    inference(resolution,[],[f37,f45])).
% 0.13/0.41  fof(f45,plain,(
% 0.13/0.41    v1_relat_1(sK2)),
% 0.13/0.41    inference(resolution,[],[f19,f23])).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f12])).
% 0.13/0.41  fof(f12,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.41    inference(ennf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.13/0.41  fof(f37,plain,(
% 0.13/0.41    ( ! [X0] : (~v1_relat_1(sK2) | k1_tarski(X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0))) )),
% 0.13/0.41    inference(resolution,[],[f17,f22])).
% 0.13/0.41  fof(f22,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_tarski(X0) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f11])).
% 0.13/0.41  fof(f11,plain,(
% 0.13/0.41    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_relat_1(X1) != k1_tarski(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.13/0.41    inference(flattening,[],[f10])).
% 0.13/0.41  fof(f10,plain,(
% 0.13/0.41    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_relat_1(X1) != k1_tarski(X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.13/0.41    inference(ennf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_tarski(X0) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    v1_funct_1(sK2)),
% 0.13/0.41    inference(cnf_transformation,[],[f9])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (19578)------------------------------
% 0.13/0.41  % (19578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (19578)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (19578)Memory used [KB]: 1663
% 0.13/0.41  % (19578)Time elapsed: 0.004 s
% 0.13/0.41  % (19578)------------------------------
% 0.13/0.41  % (19578)------------------------------
% 0.13/0.41  % (19564)Success in time 0.057 s
%------------------------------------------------------------------------------
