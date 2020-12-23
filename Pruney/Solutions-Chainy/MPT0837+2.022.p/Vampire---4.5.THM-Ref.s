%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 309 expanded)
%              Number of leaves         :    9 (  70 expanded)
%              Depth                    :   20
%              Number of atoms          :  173 (1048 expanded)
%              Number of equality atoms :   11 (  55 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(subsumption_resolution,[],[f129,f42])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f41,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f129,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f128,f120])).

fof(f120,plain,(
    r2_hidden(sK3,k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f119,f88])).

fof(f88,plain,(
    r2_hidden(sK4,sK1) ),
    inference(subsumption_resolution,[],[f87,f25])).

fof(f25,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK4,sK1) ),
    inference(resolution,[],[f86,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f86,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(subsumption_resolution,[],[f84,f69])).

fof(f69,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | m1_subset_1(sK4,sK1) ),
    inference(subsumption_resolution,[],[f68,f42])).

fof(f68,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | m1_subset_1(sK4,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | m1_subset_1(sK4,sK1)
    | ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X1,X2,X0),X2)
      | ~ r2_hidden(X1,k9_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f64,plain,(
    ! [X7] :
      ( ~ m1_subset_1(sK5(sK3,X7,sK2),sK1)
      | ~ r2_hidden(sK3,k9_relat_1(sK2,X7))
      | m1_subset_1(sK4,sK1) ) ),
    inference(subsumption_resolution,[],[f59,f42])).

fof(f59,plain,(
    ! [X7] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK3,k9_relat_1(sK2,X7))
      | ~ m1_subset_1(sK5(sK3,X7,sK2),sK1)
      | m1_subset_1(sK4,sK1) ) ),
    inference(resolution,[],[f34,f53])).

fof(f53,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK3),sK2)
      | ~ m1_subset_1(X1,sK1)
      | m1_subset_1(sK4,sK1) ) ),
    inference(resolution,[],[f21,f22])).

fof(f22,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | m1_subset_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,
    ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | m1_subset_1(sK4,sK1) ),
    inference(backward_demodulation,[],[f22,f80])).

fof(f80,plain,(
    k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f78,f70])).

fof(f70,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK1,sK0,sK2,X0) ),
    inference(resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f78,plain,(
    k2_relset_1(sK1,sK0,sK2) = k7_relset_1(sK1,sK0,sK2,sK1) ),
    inference(resolution,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f119,plain,
    ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK4,sK1) ),
    inference(factoring,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
      | r2_hidden(sK3,k9_relat_1(sK2,X0))
      | ~ r2_hidden(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK4,X0)
      | r2_hidden(sK3,k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f85,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f36,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k9_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f23,f80])).

fof(f23,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f128,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f126,f49])).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(sK3,X0,sK2),sK1)
      | ~ r2_hidden(sK3,k9_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(sK3,X0,sK2),sK1)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK3,k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f121,f34])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK3),sK2)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f120,f83])).

fof(f83,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(backward_demodulation,[],[f21,f80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:17:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (13468)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.46  % (13460)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.46  % (13460)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f130,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(subsumption_resolution,[],[f129,f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    v1_relat_1(sK2)),
% 0.19/0.46    inference(subsumption_resolution,[],[f41,f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f27,f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,negated_conjecture,(
% 0.19/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.19/0.46    inference(negated_conjecture,[],[f9])).
% 0.19/0.46  fof(f9,conjecture,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.46  fof(f129,plain,(
% 0.19/0.46    ~v1_relat_1(sK2)),
% 0.19/0.46    inference(subsumption_resolution,[],[f128,f120])).
% 0.19/0.46  fof(f120,plain,(
% 0.19/0.46    r2_hidden(sK3,k9_relat_1(sK2,sK1))),
% 0.19/0.46    inference(subsumption_resolution,[],[f119,f88])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    r2_hidden(sK4,sK1)),
% 0.19/0.46    inference(subsumption_resolution,[],[f87,f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ~v1_xboole_0(sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    v1_xboole_0(sK1) | r2_hidden(sK4,sK1)),
% 0.19/0.46    inference(resolution,[],[f86,f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    m1_subset_1(sK4,sK1)),
% 0.19/0.46    inference(subsumption_resolution,[],[f84,f69])).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | m1_subset_1(sK4,sK1)),
% 0.19/0.46    inference(subsumption_resolution,[],[f68,f42])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | m1_subset_1(sK4,sK1) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f67])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | m1_subset_1(sK4,sK1) | ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f64,f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X1,X2,X0),X2) | ~r2_hidden(X1,k9_relat_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(resolution,[],[f35,f30])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.19/0.46  fof(f64,plain,(
% 0.19/0.46    ( ! [X7] : (~m1_subset_1(sK5(sK3,X7,sK2),sK1) | ~r2_hidden(sK3,k9_relat_1(sK2,X7)) | m1_subset_1(sK4,sK1)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f59,f42])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    ( ! [X7] : (~v1_relat_1(sK2) | ~r2_hidden(sK3,k9_relat_1(sK2,X7)) | ~m1_subset_1(sK5(sK3,X7,sK2),sK1) | m1_subset_1(sK4,sK1)) )),
% 0.19/0.46    inference(resolution,[],[f34,f53])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK3),sK2) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK4,sK1)) )),
% 0.19/0.46    inference(resolution,[],[f21,f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | m1_subset_1(sK4,sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ( ! [X4] : (~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | ~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f84,plain,(
% 0.19/0.46    r2_hidden(sK3,k9_relat_1(sK2,sK1)) | m1_subset_1(sK4,sK1)),
% 0.19/0.46    inference(backward_demodulation,[],[f22,f80])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1)),
% 0.19/0.46    inference(forward_demodulation,[],[f78,f70])).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK1,sK0,sK2,X0)) )),
% 0.19/0.46    inference(resolution,[],[f39,f24])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.46  fof(f78,plain,(
% 0.19/0.46    k2_relset_1(sK1,sK0,sK2) = k7_relset_1(sK1,sK0,sK2,sK1)),
% 0.19/0.46    inference(resolution,[],[f37,f24])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.19/0.46  fof(f119,plain,(
% 0.19/0.46    r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~r2_hidden(sK4,sK1)),
% 0.19/0.46    inference(factoring,[],[f95])).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    ( ! [X0] : (r2_hidden(sK3,k9_relat_1(sK2,sK1)) | r2_hidden(sK3,k9_relat_1(sK2,X0)) | ~r2_hidden(sK4,X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f91,f42])).
% 0.19/0.46  fof(f91,plain,(
% 0.19/0.46    ( ! [X0] : (r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~r2_hidden(sK4,X0) | r2_hidden(sK3,k9_relat_1(sK2,X0))) )),
% 0.19/0.46    inference(resolution,[],[f85,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f36,f31])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(flattening,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k9_relat_1(sK2,sK1))),
% 0.19/0.46    inference(backward_demodulation,[],[f23,f80])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | r2_hidden(k4_tarski(sK4,sK3),sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f128,plain,(
% 0.19/0.46    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f127])).
% 0.19/0.46  fof(f127,plain,(
% 0.19/0.46    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f126,f49])).
% 0.19/0.46  fof(f126,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(sK5(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k9_relat_1(sK2,X0))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f125,f42])).
% 0.19/0.46  fof(f125,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(sK5(sK3,X0,sK2),sK1) | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k9_relat_1(sK2,X0))) )),
% 0.19/0.46    inference(resolution,[],[f121,f34])).
% 0.19/0.46  fof(f121,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK3),sK2) | ~m1_subset_1(X0,sK1)) )),
% 0.19/0.46    inference(resolution,[],[f120,f83])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    ( ! [X4] : (~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) )),
% 0.19/0.46    inference(backward_demodulation,[],[f21,f80])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (13460)------------------------------
% 0.19/0.46  % (13460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (13460)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (13460)Memory used [KB]: 6268
% 0.19/0.46  % (13460)Time elapsed: 0.059 s
% 0.19/0.46  % (13460)------------------------------
% 0.19/0.46  % (13460)------------------------------
% 0.19/0.47  % (13446)Success in time 0.113 s
%------------------------------------------------------------------------------
