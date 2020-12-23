%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 186 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  143 ( 604 expanded)
%              Number of equality atoms :   23 (  91 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(subsumption_resolution,[],[f119,f108])).

fof(f108,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f28,f106])).

fof(f106,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f101,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f101,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f99,f51])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f99,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f98,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f98,plain,(
    v1_xboole_0(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f97,f60])).

fof(f60,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f44,f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f97,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f96,f51])).

fof(f96,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK1)
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK1)
    | v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(resolution,[],[f72,f83])).

fof(f83,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f81,f79])).

fof(f79,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f43,f27])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f81,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) ),
    inference(backward_demodulation,[],[f54,f79])).

fof(f54,plain,
    ( ~ m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)
    | v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) ),
    inference(resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f26,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(k1_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(resolution,[],[f71,f35])).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X3))
      | m1_subset_1(X1,X2)
      | ~ v1_relat_1(X3)
      | ~ v4_relat_1(X3,X2) ) ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | m1_subset_1(X1,X3)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f28,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,(
    k1_xboole_0 = k2_relset_1(sK1,sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f114,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f114,plain,(
    k2_relat_1(k1_xboole_0) = k2_relset_1(sK1,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f74,f106])).

fof(f74,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f42,f27])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (25809)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.46  % (25809)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (25817)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f119,f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    k1_xboole_0 != k2_relset_1(sK1,sK0,k1_xboole_0)),
% 0.21/0.46    inference(backward_demodulation,[],[f28,f106])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    k1_xboole_0 = sK2),
% 0.21/0.46    inference(resolution,[],[f101,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    v1_xboole_0(sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f99,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(resolution,[],[f41,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f12])).
% 0.21/0.46  fof(f12,conjecture,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | v1_xboole_0(sK2)),
% 0.21/0.46    inference(resolution,[],[f98,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f97,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    v4_relat_1(sK2,sK1)),
% 0.21/0.46    inference(resolution,[],[f44,f27])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ~v4_relat_1(sK2,sK1) | v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f96,f51])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK1) | v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK1) | v1_xboole_0(k1_relat_1(sK2)) | v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.46    inference(resolution,[],[f72,f83])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ~m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.46    inference(forward_demodulation,[],[f81,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.46    inference(resolution,[],[f43,f27])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    v1_xboole_0(k1_relat_1(sK2)) | ~m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)),
% 0.21/0.46    inference(backward_demodulation,[],[f54,f79])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ~m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) | v1_xboole_0(k1_relset_1(sK1,sK0,sK2))),
% 0.21/0.46    inference(resolution,[],[f26,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(sK3(k1_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | v1_xboole_0(k1_relat_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f71,f35])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (~r2_hidden(X1,k1_relat_1(X3)) | m1_subset_1(X1,X2) | ~v1_relat_1(X3) | ~v4_relat_1(X3,X2)) )),
% 0.21/0.47    inference(resolution,[],[f69,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (~r1_tarski(X2,X3) | m1_subset_1(X1,X3) | ~r2_hidden(X1,X2)) )),
% 0.21/0.47    inference(resolution,[],[f46,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relset_1(sK1,sK0,k1_xboole_0)),
% 0.21/0.47    inference(forward_demodulation,[],[f114,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    k2_relat_1(k1_xboole_0) = k2_relset_1(sK1,sK0,k1_xboole_0)),
% 0.21/0.47    inference(backward_demodulation,[],[f74,f106])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.21/0.47    inference(resolution,[],[f42,f27])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25809)------------------------------
% 0.21/0.47  % (25809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25809)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25809)Memory used [KB]: 6140
% 0.21/0.47  % (25809)Time elapsed: 0.058 s
% 0.21/0.47  % (25809)------------------------------
% 0.21/0.47  % (25809)------------------------------
% 0.21/0.47  % (25795)Success in time 0.112 s
%------------------------------------------------------------------------------
