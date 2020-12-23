%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 158 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  146 ( 416 expanded)
%              Number of equality atoms :   40 ( 101 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f122,f135])).

fof(f135,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k2_zfmisc_1(sK1,sK1) != k2_zfmisc_1(sK1,sK1)
    | spl3_2 ),
    inference(forward_demodulation,[],[f124,f101])).

fof(f101,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f98,f86])).

fof(f86,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f85,f67])).

fof(f67,plain,(
    sK1 = k2_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f49,f58,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(f58,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f53,f50])).

fof(f50,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

fof(f53,plain,(
    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f31,f30,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(X2,k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f31,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f85,plain,(
    k2_relat_1(k8_relat_1(sK1,sK2)) = k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f74,f62])).

fof(f62,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f74,plain,(
    k2_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) = k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f49,f70,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f70,plain,(
    v1_relat_1(k6_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f45,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f45,plain,(
    m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f98,plain,(
    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f57,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f51,f50])).

fof(f51,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f124,plain,
    ( k2_zfmisc_1(sK1,sK1) != k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f96,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f96,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f122,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f31,f30,f92,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_1
  <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f97,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f59,f94,f90])).

fof(f59,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f29,f50])).

fof(f29,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (31356)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (31374)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (31365)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31356)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (31369)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f97,f122,f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl3_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    $false | spl3_2),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f133])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    k2_zfmisc_1(sK1,sK1) != k2_zfmisc_1(sK1,sK1) | spl3_2),
% 0.20/0.52    inference(forward_demodulation,[],[f124,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    sK1 = k2_relat_1(sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f98,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    sK1 = k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f85,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    sK1 = k2_relat_1(k8_relat_1(sK1,sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f49,f58,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k2_relat_1(k8_relat_1(X0,X1)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f53,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f30,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f31,f30,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(X2,k2_relset_1(X0,X1,X3))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    v1_relat_1(sK2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f30,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    k2_relat_1(k8_relat_1(sK1,sK2)) = k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f74,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f49,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    k2_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) = k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f49,f70,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    v1_relat_1(k6_relat_1(sK1))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f49,f45,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f31,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f57,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.20/0.52    inference(backward_demodulation,[],[f51,f50])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f30,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    k2_zfmisc_1(sK1,sK1) != k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)) | spl3_2),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f96,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 = X1 | k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 | k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    sK1 != k2_relat_1(sK2) | spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl3_2 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl3_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    $false | spl3_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f31,f30,f92,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(X2,k1_relset_1(X0,X1,X3))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | spl3_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    spl3_1 <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f59,f94,f90])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    sK1 != k2_relat_1(sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f29,f50])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (31356)------------------------------
% 0.20/0.52  % (31356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31356)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (31356)Memory used [KB]: 6268
% 0.20/0.52  % (31356)Time elapsed: 0.105 s
% 0.20/0.52  % (31356)------------------------------
% 0.20/0.52  % (31356)------------------------------
% 0.20/0.52  % (31368)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (31346)Success in time 0.167 s
%------------------------------------------------------------------------------
