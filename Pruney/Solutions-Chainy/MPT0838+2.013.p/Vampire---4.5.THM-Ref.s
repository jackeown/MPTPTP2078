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
% DateTime   : Thu Dec  3 12:57:31 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 104 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   18
%              Number of atoms          :  132 ( 363 expanded)
%              Number of equality atoms :   40 (  83 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(subsumption_resolution,[],[f93,f63])).

fof(f63,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(superposition,[],[f23,f60])).

fof(f60,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f23,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f93,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f92,f41])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f34,f22])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(superposition,[],[f26,f86])).

fof(f86,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f85,f51])).

fof(f51,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f38,f22])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f85,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f84,f41])).

fof(f84,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f83,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f83,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f82,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f82,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f72,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1)
      | k1_xboole_0 = k2_relat_1(sK2)
      | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f71,f66])).

fof(f66,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f36,f22])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK2)
      | ~ m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1)
      | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f69,f66])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1)
      | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
      | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f59,f66])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
      | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3(X0,k2_relset_1(sK0,sK1,sK2)),sK1) ) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:23:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.45  % (25318)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.18/0.46  % (25331)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.18/0.46  % (25331)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % (25339)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f94,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(subsumption_resolution,[],[f93,f63])).
% 0.18/0.46  fof(f63,plain,(
% 0.18/0.46    k1_xboole_0 != k1_relat_1(sK2)),
% 0.18/0.46    inference(superposition,[],[f23,f60])).
% 0.18/0.46  fof(f60,plain,(
% 0.18/0.46    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.18/0.46    inference(resolution,[],[f35,f22])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.46    inference(cnf_transformation,[],[f12])).
% 0.18/0.46  fof(f12,plain,(
% 0.18/0.46    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.18/0.46    inference(flattening,[],[f11])).
% 0.18/0.46  fof(f11,plain,(
% 0.18/0.46    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f10])).
% 0.18/0.46  fof(f10,negated_conjecture,(
% 0.18/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.18/0.46    inference(negated_conjecture,[],[f9])).
% 0.18/0.46  fof(f9,conjecture,(
% 0.18/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 0.18/0.46  fof(f35,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f18])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(ennf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.46  fof(f23,plain,(
% 0.18/0.46    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.18/0.46    inference(cnf_transformation,[],[f12])).
% 0.18/0.46  fof(f93,plain,(
% 0.18/0.46    k1_xboole_0 = k1_relat_1(sK2)),
% 0.18/0.46    inference(subsumption_resolution,[],[f92,f41])).
% 0.18/0.46  fof(f41,plain,(
% 0.18/0.46    v1_relat_1(sK2)),
% 0.18/0.46    inference(resolution,[],[f34,f22])).
% 0.18/0.46  fof(f34,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f17])).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(ennf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.46  fof(f92,plain,(
% 0.18/0.46    ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.18/0.46    inference(trivial_inequality_removal,[],[f89])).
% 0.18/0.46  fof(f89,plain,(
% 0.18/0.46    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.18/0.46    inference(superposition,[],[f26,f86])).
% 0.18/0.46  fof(f86,plain,(
% 0.18/0.46    k1_xboole_0 = k2_relat_1(sK2)),
% 0.18/0.46    inference(subsumption_resolution,[],[f85,f51])).
% 0.18/0.46  fof(f51,plain,(
% 0.18/0.46    v5_relat_1(sK2,sK1)),
% 0.18/0.46    inference(resolution,[],[f38,f22])).
% 0.18/0.46  fof(f38,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(ennf_transformation,[],[f6])).
% 0.18/0.46  fof(f6,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.46  fof(f85,plain,(
% 0.18/0.46    k1_xboole_0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK1)),
% 0.18/0.46    inference(subsumption_resolution,[],[f84,f41])).
% 0.18/0.46  fof(f84,plain,(
% 0.18/0.46    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,sK1)),
% 0.18/0.46    inference(resolution,[],[f83,f29])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f14])).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.18/0.46  fof(f83,plain,(
% 0.18/0.46    ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.18/0.46    inference(resolution,[],[f82,f32])).
% 0.18/0.46  fof(f32,plain,(
% 0.18/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.18/0.46  fof(f82,plain,(
% 0.18/0.46    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.18/0.46    inference(duplicate_literal_removal,[],[f81])).
% 0.18/0.46  fof(f81,plain,(
% 0.18/0.46    k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.18/0.46    inference(resolution,[],[f72,f30])).
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f16])).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.46    inference(flattening,[],[f15])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.18/0.46  fof(f72,plain,(
% 0.18/0.46    ( ! [X0] : (~m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1) | k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))) )),
% 0.18/0.46    inference(forward_demodulation,[],[f71,f66])).
% 0.18/0.46  fof(f66,plain,(
% 0.18/0.46    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.18/0.46    inference(resolution,[],[f36,f22])).
% 0.18/0.46  fof(f36,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f19])).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(ennf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.46  fof(f71,plain,(
% 0.18/0.46    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0))) )),
% 0.18/0.46    inference(forward_demodulation,[],[f69,f66])).
% 0.18/0.46  fof(f69,plain,(
% 0.18/0.46    ( ! [X0] : (~m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1) | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0))) )),
% 0.18/0.46    inference(backward_demodulation,[],[f59,f66])).
% 0.18/0.46  fof(f59,plain,(
% 0.18/0.46    ( ! [X0] : (k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k2_relset_1(sK0,sK1,sK2)),sK1)) )),
% 0.18/0.46    inference(resolution,[],[f31,f21])).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f12])).
% 0.18/0.46  fof(f31,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f16])).
% 0.18/0.46  fof(f26,plain,(
% 0.18/0.46    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f13])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (25331)------------------------------
% 0.18/0.46  % (25331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (25331)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (25331)Memory used [KB]: 6140
% 0.18/0.46  % (25331)Time elapsed: 0.053 s
% 0.18/0.46  % (25331)------------------------------
% 0.18/0.46  % (25331)------------------------------
% 0.18/0.47  % (25317)Success in time 0.12 s
%------------------------------------------------------------------------------
