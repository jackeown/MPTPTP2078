%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 118 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 218 expanded)
%              Number of equality atoms :   41 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f66,f81,f90,f116,f118])).

fof(f118,plain,
    ( ~ spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f117,f48,f113])).

fof(f113,plain,
    ( spl2_6
  <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f48,plain,
    ( spl2_1
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f117,plain,
    ( sK1 != k10_relat_1(k6_partfun1(sK0),sK1)
    | spl2_1 ),
    inference(superposition,[],[f50,f91])).

fof(f91,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f50,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f116,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f111,f87,f113])).

fof(f87,plain,
    ( spl2_5
  <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f111,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f109,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f26,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f109,plain,
    ( k10_relat_1(k6_partfun1(sK0),sK1) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f105,f89])).

fof(f89,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f105,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k7_relat_1(k6_partfun1(X1),X0)) ),
    inference(forward_demodulation,[],[f84,f72])).

fof(f72,plain,(
    ! [X0,X1] : k7_relat_1(k6_partfun1(X0),X1) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ),
    inference(unit_resulting_resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f35,f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f84,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f82,f45])).

fof(f82,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) ),
    inference(unit_resulting_resolution,[],[f43,f43,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f90,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f85,f78,f87])).

fof(f78,plain,
    ( spl2_4
  <=> v4_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f85,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f43,f80,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f80,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f81,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f74,f62,f78])).

fof(f62,plain,
    ( spl2_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f74,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f64,f42,f43,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f42,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f66,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f59,f53,f62])).

fof(f53,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f59,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f56,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f51,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (18615)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.44  % (18615)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f51,f56,f66,f81,f90,f116,f118])).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    ~spl2_6 | spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f117,f48,f113])).
% 0.22/0.44  fof(f113,plain,(
% 0.22/0.44    spl2_6 <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl2_1 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) | spl2_1),
% 0.22/0.44    inference(superposition,[],[f50,f91])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f31,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f48])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    spl2_6 | ~spl2_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f111,f87,f113])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    spl2_5 <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f111,plain,(
% 0.22/0.44    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | ~spl2_5),
% 0.22/0.44    inference(forward_demodulation,[],[f109,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.22/0.44    inference(definition_unfolding,[],[f32,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.44  fof(f109,plain,(
% 0.22/0.44    k10_relat_1(k6_partfun1(sK0),sK1) = k1_relat_1(k6_partfun1(sK1)) | ~spl2_5),
% 0.22/0.44    inference(superposition,[],[f105,f89])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) | ~spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f87])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k7_relat_1(k6_partfun1(X1),X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f84,f72])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k7_relat_1(k6_partfun1(X0),X1) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f43,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f35,f26])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f27,f26])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f82,f45])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1)))) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f43,f43,f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    spl2_5 | ~spl2_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f85,f78,f87])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl2_4 <=> v4_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) | ~spl2_4),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f43,f80,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    v4_relat_1(k6_partfun1(sK1),sK0) | ~spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f78])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    spl2_4 | ~spl2_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f74,f62,f78])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl2_3 <=> r1_tarski(sK1,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    v4_relat_1(k6_partfun1(sK1),sK0) | ~spl2_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f64,f42,f43,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f28,f26])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    r1_tarski(sK1,sK0) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f62])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl2_3 | ~spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f59,f53,f62])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    r1_tarski(sK1,sK0) | ~spl2_2),
% 0.22/0.44    inference(resolution,[],[f38,f55])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.44    inference(nnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f53])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.44    inference(negated_conjecture,[],[f11])).
% 0.22/0.44  fof(f11,conjecture,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ~spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f48])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f22])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (18615)------------------------------
% 0.22/0.44  % (18615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (18615)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (18615)Memory used [KB]: 6140
% 0.22/0.44  % (18615)Time elapsed: 0.011 s
% 0.22/0.44  % (18615)------------------------------
% 0.22/0.44  % (18615)------------------------------
% 0.22/0.44  % (18603)Success in time 0.078 s
%------------------------------------------------------------------------------
