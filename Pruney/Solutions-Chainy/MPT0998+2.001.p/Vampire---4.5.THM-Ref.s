%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 254 expanded)
%              Number of leaves         :    6 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  197 (1184 expanded)
%              Number of equality atoms :   45 ( 237 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f108,f20])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
                & r2_hidden(X4,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
          <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).

fof(f108,plain,(
    ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f107,f60])).

fof(f60,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f22,f30])).

fof(f30,plain,(
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

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f106,f94])).

fof(f94,plain,(
    r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f93,f88])).

fof(f88,plain,(
    r2_hidden(sK4,sK0) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,
    ( r2_hidden(sK4,sK0)
    | r2_hidden(sK4,sK0) ),
    inference(forward_demodulation,[],[f86,f64])).

fof(f64,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f59,f55])).

fof(f55,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f54,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f53,f22])).

fof(f53,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f21,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f21,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f22,f31])).

fof(f31,plain,(
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

fof(f86,plain,
    ( r2_hidden(sK4,sK0)
    | r2_hidden(sK4,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f85,f20])).

fof(f85,plain,
    ( r2_hidden(sK4,sK0)
    | ~ v1_funct_1(sK3)
    | r2_hidden(sK4,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f80,f60])).

fof(f80,plain,
    ( r2_hidden(sK4,sK0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | r2_hidden(sK4,k1_relat_1(sK3)) ),
    inference(resolution,[],[f62,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f62,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | r2_hidden(sK4,sK0) ),
    inference(backward_demodulation,[],[f18,f56])).

fof(f56,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(resolution,[],[f22,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f18,plain,
    ( r2_hidden(sK4,sK0)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,
    ( ~ r2_hidden(sK4,sK0)
    | r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    inference(forward_demodulation,[],[f92,f64])).

fof(f92,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ r2_hidden(sK4,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f91,f20])).

fof(f91,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK4,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f90,f60])).

fof(f90,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK4,k1_relat_1(sK3)) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f19,f56])).

fof(f19,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f106,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f105,f88])).

fof(f105,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f17,f56])).

fof(f17,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (8722)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (8722)Refutation not found, incomplete strategy% (8722)------------------------------
% 0.21/0.44  % (8722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (8722)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (8722)Memory used [KB]: 10618
% 0.21/0.44  % (8722)Time elapsed: 0.040 s
% 0.21/0.44  % (8722)------------------------------
% 0.21/0.44  % (8722)------------------------------
% 0.21/0.45  % (8715)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.45  % (8715)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f108,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    v1_funct_1(sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <~> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.45    inference(flattening,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : ((? [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <~> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    ~v1_funct_1(sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f107,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    v1_relat_1(sK3)),
% 0.21/0.45    inference(resolution,[],[f22,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    ~v1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f106,f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK2))),
% 0.21/0.45    inference(subsumption_resolution,[],[f93,f88])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    r2_hidden(sK4,sK0)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    r2_hidden(sK4,sK0) | r2_hidden(sK4,sK0)),
% 0.21/0.45    inference(forward_demodulation,[],[f86,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    sK0 = k1_relat_1(sK3)),
% 0.21/0.45    inference(forward_demodulation,[],[f59,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f54,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    k1_xboole_0 != sK1),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f53,f22])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    inference(resolution,[],[f21,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    inference(resolution,[],[f22,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    r2_hidden(sK4,sK0) | r2_hidden(sK4,k1_relat_1(sK3))),
% 0.21/0.45    inference(subsumption_resolution,[],[f85,f20])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    r2_hidden(sK4,sK0) | ~v1_funct_1(sK3) | r2_hidden(sK4,k1_relat_1(sK3))),
% 0.21/0.45    inference(subsumption_resolution,[],[f80,f60])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    r2_hidden(sK4,sK0) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | r2_hidden(sK4,k1_relat_1(sK3))),
% 0.21/0.45    inference(resolution,[],[f62,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.45    inference(equality_resolution,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | r2_hidden(sK4,sK0)),
% 0.21/0.45    inference(backward_demodulation,[],[f18,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X0] : (k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)) )),
% 0.21/0.45    inference(resolution,[],[f22,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    r2_hidden(sK4,sK0) | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ~r2_hidden(sK4,sK0) | r2_hidden(sK4,k10_relat_1(sK3,sK2))),
% 0.21/0.45    inference(forward_demodulation,[],[f92,f64])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~r2_hidden(sK4,k1_relat_1(sK3))),
% 0.21/0.45    inference(subsumption_resolution,[],[f91,f20])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~r2_hidden(sK4,k1_relat_1(sK3))),
% 0.21/0.45    inference(subsumption_resolution,[],[f90,f60])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r2_hidden(sK4,k1_relat_1(sK3))),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r2_hidden(sK4,k1_relat_1(sK3)) | r2_hidden(sK4,k10_relat_1(sK3,sK2))),
% 0.21/0.45    inference(resolution,[],[f63,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X0,X3),X1) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.45    inference(equality_resolution,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X0,X3),X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    r2_hidden(k1_funct_1(sK3,sK4),sK2) | r2_hidden(sK4,k10_relat_1(sK3,sK2))),
% 0.21/0.45    inference(backward_demodulation,[],[f19,f56])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    r2_hidden(k1_funct_1(sK3,sK4),sK2) | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    ~r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f105,f88])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    ~r2_hidden(sK4,sK0) | ~r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f104])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    ~r2_hidden(sK4,sK0) | ~r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK2))),
% 0.21/0.45    inference(resolution,[],[f61,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.45    inference(equality_resolution,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK4,sK0) | ~r2_hidden(sK4,k10_relat_1(sK3,sK2))),
% 0.21/0.45    inference(backward_demodulation,[],[f17,f56])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ~r2_hidden(sK4,sK0) | ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (8715)------------------------------
% 0.21/0.45  % (8715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (8715)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (8715)Memory used [KB]: 1663
% 0.21/0.45  % (8715)Time elapsed: 0.049 s
% 0.21/0.45  % (8715)------------------------------
% 0.21/0.45  % (8715)------------------------------
% 0.21/0.45  % (8701)Success in time 0.098 s
%------------------------------------------------------------------------------
