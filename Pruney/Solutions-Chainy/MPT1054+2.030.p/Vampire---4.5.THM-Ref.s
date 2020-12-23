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
% DateTime   : Thu Dec  3 13:07:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  71 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 125 expanded)
%              Number of equality atoms :   33 (  51 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f73,f80])).

fof(f80,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f78,f72])).

fof(f72,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_4
  <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f78,plain,
    ( sK1 != k10_relat_1(k6_partfun1(sK0),sK1)
    | spl2_2 ),
    inference(superposition,[],[f45,f67])).

fof(f67,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f27,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f27,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f45,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_2
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f73,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f63,f38,f70])).

fof(f38,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k10_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(backward_demodulation,[],[f36,f58])).

fof(f58,plain,(
    ! [X0,X1] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f56,f31])).

fof(f31,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f21,f20,f20])).

fof(f20,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f21,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f56,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) ),
    inference(unit_resulting_resolution,[],[f33,f32,f34,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f34,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f25,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f32,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f28,f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

% (28178)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f46,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:04:11 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.41  % (28186)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.41  % (28186)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f81,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f41,f46,f73,f80])).
% 0.19/0.41  fof(f80,plain,(
% 0.19/0.41    spl2_2 | ~spl2_4),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f79])).
% 0.19/0.41  fof(f79,plain,(
% 0.19/0.41    $false | (spl2_2 | ~spl2_4)),
% 0.19/0.41    inference(subsumption_resolution,[],[f78,f72])).
% 0.19/0.41  fof(f72,plain,(
% 0.19/0.41    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | ~spl2_4),
% 0.19/0.41    inference(avatar_component_clause,[],[f70])).
% 0.19/0.41  fof(f70,plain,(
% 0.19/0.41    spl2_4 <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.41  fof(f78,plain,(
% 0.19/0.41    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) | spl2_2),
% 0.19/0.41    inference(superposition,[],[f45,f67])).
% 0.19/0.41  fof(f67,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f27,f30])).
% 0.19/0.41  fof(f30,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f15])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.41    inference(ennf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.19/0.41  fof(f27,plain,(
% 0.19/0.41    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,axiom,(
% 0.19/0.41    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.19/0.41  fof(f45,plain,(
% 0.19/0.41    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_2),
% 0.19/0.41    inference(avatar_component_clause,[],[f43])).
% 0.19/0.41  fof(f43,plain,(
% 0.19/0.41    spl2_2 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.41  fof(f73,plain,(
% 0.19/0.41    spl2_4 | ~spl2_1),
% 0.19/0.41    inference(avatar_split_clause,[],[f63,f38,f70])).
% 0.19/0.41  fof(f38,plain,(
% 0.19/0.41    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.41  fof(f63,plain,(
% 0.19/0.41    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | ~spl2_1),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f40,f59])).
% 0.19/0.41  fof(f59,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k10_relat_1(k6_partfun1(X0),X1) = X1) )),
% 0.19/0.41    inference(backward_demodulation,[],[f36,f58])).
% 0.19/0.41  fof(f58,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.19/0.41    inference(forward_demodulation,[],[f56,f31])).
% 0.19/0.41  fof(f31,plain,(
% 0.19/0.41    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f21,f20,f20])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f8])).
% 0.19/0.41  fof(f8,axiom,(
% 0.19/0.41    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.19/0.41  fof(f56,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1)) )),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f33,f32,f34,f29])).
% 0.19/0.41  fof(f29,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.41    inference(flattening,[],[f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.41    inference(ennf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.19/0.41  fof(f34,plain,(
% 0.19/0.41    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f25,f20])).
% 0.19/0.41  fof(f25,plain,(
% 0.19/0.41    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f23,f20])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.41  fof(f33,plain,(
% 0.19/0.41    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f22,f20])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f36,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = X1) )),
% 0.19/0.41    inference(definition_unfolding,[],[f28,f20])).
% 0.19/0.41  fof(f28,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  % (28178)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f38])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ~spl2_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f19,f43])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.19/0.42    inference(negated_conjecture,[],[f9])).
% 0.19/0.42  fof(f9,conjecture,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    spl2_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f18,f38])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.42    inference(cnf_transformation,[],[f17])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (28186)------------------------------
% 0.19/0.42  % (28186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (28186)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (28186)Memory used [KB]: 10618
% 0.19/0.42  % (28186)Time elapsed: 0.009 s
% 0.19/0.42  % (28186)------------------------------
% 0.19/0.42  % (28186)------------------------------
% 0.19/0.42  % (28170)Success in time 0.075 s
%------------------------------------------------------------------------------
