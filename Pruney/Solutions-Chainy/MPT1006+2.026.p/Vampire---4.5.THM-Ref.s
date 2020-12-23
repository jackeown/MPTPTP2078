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
% DateTime   : Thu Dec  3 13:03:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 143 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 ( 300 expanded)
%              Number of equality atoms :   65 ( 128 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f163,f176,f178])).

fof(f178,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f68,f97])).

fof(f97,plain,
    ( ! [X2] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_1
  <=> ! [X2] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f22,f65])).

fof(f65,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f64,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f29,f59])).

fof(f59,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(resolution,[],[f31,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f23,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f22,plain,(
    v1_funct_2(sK2,k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f176,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f174,f99,f96])).

fof(f99,plain,
    ( spl3_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f174,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ) ),
    inference(backward_demodulation,[],[f171,f173])).

fof(f173,plain,(
    ! [X4] : k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f157,f75])).

fof(f75,plain,(
    ! [X4,X3] : k1_relset_1(X3,X4,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f157,plain,(
    ! [X4,X3] : k1_relset_1(X3,X4,k1_xboole_0) = k10_relat_1(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f154,f117])).

fof(f117,plain,(
    ! [X6,X4,X5] : k8_relset_1(X4,X5,k1_xboole_0,X6) = k10_relat_1(k1_xboole_0,X6) ),
    inference(resolution,[],[f44,f26])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f154,plain,(
    ! [X4,X3] : k1_relset_1(X3,X4,k1_xboole_0) = k8_relset_1(X3,X4,k1_xboole_0,X4) ),
    inference(resolution,[],[f37,f26])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f171,plain,(
    ! [X1] :
      ( k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f105,f157])).

fof(f105,plain,(
    ! [X1] :
      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ v1_funct_2(X1,k1_xboole_0,X0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f49,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f163,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f69,f160])).

fof(f160,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k8_relset_1(X4,X5,k1_xboole_0,X6)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f117,f158])).

fof(f158,plain,
    ( ! [X4] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X4)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f157,f103])).

fof(f103,plain,
    ( ! [X4,X3] : k1_xboole_0 = k1_relset_1(X3,X4,k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f75,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f69,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f24,f65])).

fof(f24,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:04:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (15535)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (15535)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f163,f176,f178])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ~spl3_1),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    $false | ~spl3_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f68,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X2] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) ) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl3_1 <=> ! [X2] : ~v1_funct_2(k1_xboole_0,k1_xboole_0,X2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.22/0.50    inference(backward_demodulation,[],[f22,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k1_xboole_0 = sK2),
% 0.22/0.50    inference(subsumption_resolution,[],[f64,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 0.22/0.50    inference(resolution,[],[f29,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    r1_tarski(sK2,k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f31,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    inference(backward_demodulation,[],[f23,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    v1_funct_2(sK2,k1_xboole_0,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    spl3_1 | spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f174,f99,f96])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f171,f173])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X4] : (k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,X4)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f157,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k1_relset_1(X3,X4,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f35,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k1_relset_1(X3,X4,k1_xboole_0) = k10_relat_1(k1_xboole_0,X4)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f154,f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X6,X4,X5] : (k8_relset_1(X4,X5,k1_xboole_0,X6) = k10_relat_1(k1_xboole_0,X6)) )),
% 0.22/0.50    inference(resolution,[],[f44,f26])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k1_relset_1(X3,X4,k1_xboole_0) = k8_relset_1(X3,X4,k1_xboole_0,X4)) )),
% 0.22/0.50    inference(resolution,[],[f37,f26])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X1) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f105,f157])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X1] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f92,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~v1_funct_2(X1,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f55,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f49,f48])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    ~spl3_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    $false | ~spl3_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f69,f160])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    ( ! [X6,X4,X5] : (k1_xboole_0 = k8_relset_1(X4,X5,k1_xboole_0,X6)) ) | ~spl3_2),
% 0.22/0.50    inference(backward_demodulation,[],[f117,f158])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ( ! [X4] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X4)) ) | ~spl3_2),
% 0.22/0.50    inference(forward_demodulation,[],[f157,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k1_xboole_0 = k1_relset_1(X3,X4,k1_xboole_0)) ) | ~spl3_2),
% 0.22/0.50    inference(backward_demodulation,[],[f75,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.22/0.50    inference(backward_demodulation,[],[f24,f65])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15535)------------------------------
% 0.22/0.50  % (15535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15535)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15535)Memory used [KB]: 10746
% 0.22/0.50  % (15535)Time elapsed: 0.053 s
% 0.22/0.50  % (15535)------------------------------
% 0.22/0.50  % (15535)------------------------------
% 0.22/0.50  % (15510)Success in time 0.141 s
%------------------------------------------------------------------------------
