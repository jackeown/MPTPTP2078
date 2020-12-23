%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 468 expanded)
%              Number of leaves         :    5 (  84 expanded)
%              Depth                    :   27
%              Number of atoms          :  201 (2674 expanded)
%              Number of equality atoms :   89 ( 837 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f18])).

fof(f18,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f87,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f86,f17])).

fof(f17,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,
    ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f82,f64])).

fof(f64,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f16,f62])).

fof(f62,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f61,f18])).

fof(f61,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f60,plain,
    ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f56,f16])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK2 = X0
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f55,f15])).

fof(f15,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f54,f22])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f53,f48])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f52,f19])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f24,f50])).

fof(f50,plain,
    ( sK0 = k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f46,f49])).

fof(f49,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f21,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f46,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f20,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f20,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f16,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK2 = X0 ) ),
    inference(resolution,[],[f76,f63])).

fof(f63,plain,(
    r2_hidden(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f15,f62])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f75,f22])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f74,f48])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f73,f19])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f24,f72])).

fof(f72,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f67,f71])).

fof(f71,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f68,f66])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f21,f62])).

fof(f68,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f62])).

fof(f67,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f49,f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:29:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.42  % (13190)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.43  % (13190)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % (13207)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.44  % (13198)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f88,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(subsumption_resolution,[],[f87,f18])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    sK2 != sK3),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f8,plain,(
% 0.19/0.44    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.44    inference(flattening,[],[f7])).
% 0.19/0.44  fof(f7,plain,(
% 0.19/0.44    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.19/0.44    inference(negated_conjecture,[],[f5])).
% 0.19/0.44  fof(f5,conjecture,(
% 0.19/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.19/0.44  fof(f87,plain,(
% 0.19/0.44    sK2 = sK3),
% 0.19/0.44    inference(subsumption_resolution,[],[f86,f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f86,plain,(
% 0.19/0.44    k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) | sK2 = sK3),
% 0.19/0.44    inference(resolution,[],[f82,f64])).
% 0.19/0.44  fof(f64,plain,(
% 0.19/0.44    r2_hidden(sK3,k1_xboole_0)),
% 0.19/0.44    inference(backward_demodulation,[],[f16,f62])).
% 0.19/0.44  fof(f62,plain,(
% 0.19/0.44    k1_xboole_0 = sK0),
% 0.19/0.44    inference(subsumption_resolution,[],[f61,f18])).
% 0.19/0.44  fof(f61,plain,(
% 0.19/0.44    sK2 = sK3 | k1_xboole_0 = sK0),
% 0.19/0.44    inference(subsumption_resolution,[],[f60,f17])).
% 0.19/0.44  fof(f60,plain,(
% 0.19/0.44    k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.19/0.44    inference(resolution,[],[f56,f16])).
% 0.19/0.44  fof(f56,plain,(
% 0.19/0.44    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK2 = X0 | k1_xboole_0 = sK0) )),
% 0.19/0.44    inference(resolution,[],[f55,f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    r2_hidden(sK2,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f55,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | k1_xboole_0 = sK0) )),
% 0.19/0.44    inference(subsumption_resolution,[],[f54,f22])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    v2_funct_1(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f54,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1) | k1_xboole_0 = sK0) )),
% 0.19/0.44    inference(subsumption_resolution,[],[f53,f48])).
% 0.19/0.44  fof(f48,plain,(
% 0.19/0.44    v1_relat_1(sK1)),
% 0.19/0.44    inference(resolution,[],[f21,f29])).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f53,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1) | k1_xboole_0 = sK0) )),
% 0.19/0.44    inference(subsumption_resolution,[],[f52,f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    v1_funct_1(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f52,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1) | k1_xboole_0 = sK0) )),
% 0.19/0.44    inference(superposition,[],[f24,f50])).
% 0.19/0.44  fof(f50,plain,(
% 0.19/0.44    sK0 = k1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.19/0.44    inference(superposition,[],[f46,f49])).
% 0.19/0.44  fof(f49,plain,(
% 0.19/0.44    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.19/0.44    inference(resolution,[],[f21,f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f9])).
% 0.19/0.44  fof(f9,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.44  fof(f46,plain,(
% 0.19/0.44    sK0 = k1_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0),
% 0.19/0.44    inference(subsumption_resolution,[],[f45,f21])).
% 0.19/0.44  fof(f45,plain,(
% 0.19/0.44    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.44    inference(resolution,[],[f20,f35])).
% 0.19/0.44  fof(f35,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(flattening,[],[f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f11])).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(flattening,[],[f10])).
% 0.19/0.44  fof(f10,plain,(
% 0.19/0.44    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    r2_hidden(sK3,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f82,plain,(
% 0.19/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK2 = X0) )),
% 0.19/0.44    inference(resolution,[],[f76,f63])).
% 0.19/0.44  fof(f63,plain,(
% 0.19/0.44    r2_hidden(sK2,k1_xboole_0)),
% 0.19/0.44    inference(backward_demodulation,[],[f15,f62])).
% 0.19/0.44  fof(f76,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1) )),
% 0.19/0.44    inference(subsumption_resolution,[],[f75,f22])).
% 0.19/0.44  fof(f75,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.19/0.44    inference(subsumption_resolution,[],[f74,f48])).
% 0.19/0.44  fof(f74,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.19/0.44    inference(subsumption_resolution,[],[f73,f19])).
% 0.19/0.44  fof(f73,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.19/0.44    inference(superposition,[],[f24,f72])).
% 0.19/0.44  fof(f72,plain,(
% 0.19/0.44    k1_xboole_0 = k1_relat_1(sK1)),
% 0.19/0.44    inference(backward_demodulation,[],[f67,f71])).
% 0.19/0.44  fof(f71,plain,(
% 0.19/0.44    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.19/0.44    inference(subsumption_resolution,[],[f68,f66])).
% 0.19/0.44  fof(f66,plain,(
% 0.19/0.44    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.19/0.44    inference(backward_demodulation,[],[f21,f62])).
% 0.19/0.44  fof(f68,plain,(
% 0.19/0.44    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.19/0.44    inference(resolution,[],[f65,f36])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.19/0.44    inference(equality_resolution,[],[f33])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f65,plain,(
% 0.19/0.44    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.19/0.44    inference(backward_demodulation,[],[f20,f62])).
% 0.19/0.44  fof(f67,plain,(
% 0.19/0.44    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.19/0.44    inference(backward_demodulation,[],[f49,f62])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (13190)------------------------------
% 0.19/0.44  % (13190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (13190)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (13190)Memory used [KB]: 6140
% 0.19/0.44  % (13190)Time elapsed: 0.056 s
% 0.19/0.44  % (13190)------------------------------
% 0.19/0.44  % (13190)------------------------------
% 0.19/0.44  % (13184)Success in time 0.101 s
%------------------------------------------------------------------------------
