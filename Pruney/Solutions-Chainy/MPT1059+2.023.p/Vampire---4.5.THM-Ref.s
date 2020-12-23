%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 128 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  198 ( 598 expanded)
%              Number of equality atoms :   57 ( 113 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f78,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f31,f75])).

fof(f75,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f74,f72])).

fof(f72,plain,(
    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) ),
    inference(backward_demodulation,[],[f27,f71])).

fof(f71,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f65,f26])).

fof(f26,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f63,f29])).

fof(f29,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) ) ),
    inference(resolution,[],[f46,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f27,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    r2_hidden(sK3,sK0) ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f54,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK3,sK0) ),
    inference(resolution,[],[f36,f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f68,f69])).

fof(f69,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f61,f58])).

fof(f58,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f61,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f45,f30])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f67,f28])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f66,f53])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f52,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) ) ),
    inference(resolution,[],[f57,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f57,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f39,f30])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:02:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.42  % (15805)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.43  % (15815)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.44  % (15815)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f78,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    inference(backward_demodulation,[],[f31,f75])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    k1_xboole_0 = sK1),
% 0.20/0.44    inference(subsumption_resolution,[],[f74,f72])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)),
% 0.20/0.44    inference(backward_demodulation,[],[f27,f71])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.20/0.44    inference(resolution,[],[f65,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    m1_subset_1(sK3,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f64,f32])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ~v1_xboole_0(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f63,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f62,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    v1_funct_1(sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) )),
% 0.20/0.44    inference(resolution,[],[f46,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) | k1_xboole_0 = sK1),
% 0.20/0.44    inference(resolution,[],[f73,f56])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    r2_hidden(sK3,sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f54,f32])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    v1_xboole_0(sK0) | r2_hidden(sK3,sK0)),
% 0.20/0.44    inference(resolution,[],[f36,f26])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) | k1_xboole_0 = sK1) )),
% 0.20/0.44    inference(superposition,[],[f68,f69])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.20/0.44    inference(superposition,[],[f61,f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.44    inference(resolution,[],[f38,f30])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.20/0.44    inference(subsumption_resolution,[],[f60,f29])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.44    inference(resolution,[],[f45,f30])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(flattening,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f67,f28])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f66,f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    v1_relat_1(sK2)),
% 0.20/0.44    inference(subsumption_resolution,[],[f52,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.20/0.44    inference(resolution,[],[f34,f30])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) )),
% 0.20/0.44    inference(resolution,[],[f57,f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    v5_relat_1(sK2,sK1)),
% 0.20/0.44    inference(resolution,[],[f39,f30])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.44    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ~v1_xboole_0(sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (15815)------------------------------
% 0.20/0.44  % (15815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (15815)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (15815)Memory used [KB]: 1663
% 0.20/0.44  % (15815)Time elapsed: 0.048 s
% 0.20/0.44  % (15815)------------------------------
% 0.20/0.44  % (15815)------------------------------
% 0.20/0.45  % (15797)Success in time 0.103 s
%------------------------------------------------------------------------------
