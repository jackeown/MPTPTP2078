%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t171_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:36 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  234 ( 508 expanded)
%              Number of leaves         :   64 ( 196 expanded)
%              Depth                    :   25
%              Number of atoms          :  564 (1123 expanded)
%              Number of equality atoms :   69 ( 140 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1047,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f124,f131,f139,f149,f168,f190,f200,f210,f212,f226,f236,f247,f262,f272,f280,f293,f314,f365,f379,f391,f402,f405,f415,f425,f441,f451,f458,f476,f567,f1046])).

fof(f1046,plain,
    ( ~ spl3_8
    | spl3_73 ),
    inference(avatar_contradiction_clause,[],[f1045])).

fof(f1045,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f1036,f566])).

fof(f566,plain,
    ( k10_relat_1(k6_partfun1(sK0),sK1) != sK1
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl3_73
  <=> k10_relat_1(k6_partfun1(sK0),sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f1036,plain,
    ( k10_relat_1(k6_partfun1(sK0),sK1) = sK1
    | ~ spl3_8 ),
    inference(resolution,[],[f1011,f148])).

fof(f148,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1011,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k10_relat_1(k6_partfun1(X3),X2) = X2 ) ),
    inference(forward_demodulation,[],[f1010,f544])).

fof(f544,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f102,f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',dt_k6_partfun1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',redefinition_k8_relset_1)).

fof(f1010,plain,(
    ! [X2,X3] :
      ( k8_relset_1(X3,X3,k6_partfun1(X3),X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f1009,f248])).

fof(f248,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),k8_relset_1(X0,X0,k6_partfun1(X0),X1)) ),
    inference(resolution,[],[f229,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(forward_demodulation,[],[f86,f71])).

fof(f71,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',redefinition_k6_partfun1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t162_funct_1)).

fof(f229,plain,(
    ! [X4,X3] : m1_subset_1(k8_relset_1(X3,X3,k6_partfun1(X3),X4),k1_zfmisc_1(X3)) ),
    inference(resolution,[],[f99,f78])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',dt_k8_relset_1)).

fof(f1009,plain,(
    ! [X2,X3] :
      ( k9_relat_1(k6_partfun1(X3),k8_relset_1(X3,X3,k6_partfun1(X3),X2)) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f1008,f487])).

fof(f487,plain,(
    ! [X0,X1] : k7_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f101,f78])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',redefinition_k7_relset_1)).

fof(f1008,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k7_relset_1(X3,X3,k6_partfun1(X3),k8_relset_1(X3,X3,k6_partfun1(X3),X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f1007,f108])).

fof(f108,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f76,f71])).

fof(f76,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',fc3_funct_1)).

fof(f1007,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k7_relset_1(X3,X3,k6_partfun1(X3),k8_relset_1(X3,X3,k6_partfun1(X3),X2)) = X2
      | ~ v1_funct_1(k6_partfun1(X3)) ) ),
    inference(subsumption_resolution,[],[f1006,f990])).

fof(f990,plain,(
    ! [X0] : v1_funct_2(k6_partfun1(X0),X0,X0) ),
    inference(subsumption_resolution,[],[f989,f77])).

fof(f77,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f989,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(X0),X0,X0)
      | ~ v1_partfun1(k6_partfun1(X0),X0) ) ),
    inference(resolution,[],[f428,f78])).

fof(f428,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k6_partfun1(X0),X1,X2)
      | ~ v1_partfun1(k6_partfun1(X0),X1) ) ),
    inference(resolution,[],[f94,f108])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',cc1_funct_2)).

fof(f1006,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k7_relset_1(X3,X3,k6_partfun1(X3),k8_relset_1(X3,X3,k6_partfun1(X3),X2)) = X2
      | ~ v1_funct_2(k6_partfun1(X3),X3,X3)
      | ~ v1_funct_1(k6_partfun1(X3)) ) ),
    inference(subsumption_resolution,[],[f1000,f78])).

fof(f1000,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ m1_subset_1(k6_partfun1(X3),k1_zfmisc_1(k2_zfmisc_1(X3,X3)))
      | k7_relset_1(X3,X3,k6_partfun1(X3),k8_relset_1(X3,X3,k6_partfun1(X3),X2)) = X2
      | ~ v1_funct_2(k6_partfun1(X3),X3,X3)
      | ~ v1_funct_1(k6_partfun1(X3)) ) ),
    inference(resolution,[],[f998,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
        & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 )
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
        & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 )
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t92_funct_2)).

fof(f998,plain,(
    ! [X0] : v3_funct_2(k6_partfun1(X0),X0,X0) ),
    inference(subsumption_resolution,[],[f997,f104])).

fof(f104,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f70,f71])).

fof(f70,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',dt_k6_relat_1)).

fof(f997,plain,(
    ! [X0] :
      ( v3_funct_2(k6_partfun1(X0),X0,X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f996,f106])).

fof(f106,plain,(
    ! [X0] : v3_relat_2(k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f73,f71])).

fof(f73,plain,(
    ! [X0] : v3_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v8_relat_2(k6_relat_1(X0))
      & v3_relat_2(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( v8_relat_2(k6_relat_1(X0))
      & v4_relat_2(k6_relat_1(X0))
      & v3_relat_2(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',fc3_partfun1)).

fof(f996,plain,(
    ! [X0] :
      ( v3_funct_2(k6_partfun1(X0),X0,X0)
      | ~ v3_relat_2(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f995,f105])).

fof(f105,plain,(
    ! [X0] : v8_relat_2(k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f74,f71])).

fof(f74,plain,(
    ! [X0] : v8_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f995,plain,(
    ! [X0] :
      ( v3_funct_2(k6_partfun1(X0),X0,X0)
      | ~ v8_relat_2(k6_partfun1(X0))
      | ~ v3_relat_2(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f994,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( v8_relat_2(X0)
        & v3_relat_2(X0)
        & v1_relat_1(X0) )
     => ( v1_relat_2(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',cc3_partfun1)).

fof(f994,plain,(
    ! [X0] :
      ( ~ v1_relat_2(k6_partfun1(X0))
      | v3_funct_2(k6_partfun1(X0),X0,X0) ) ),
    inference(subsumption_resolution,[],[f993,f78])).

fof(f993,plain,(
    ! [X0] :
      ( v3_funct_2(k6_partfun1(X0),X0,X0)
      | ~ v1_relat_2(k6_partfun1(X0))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(subsumption_resolution,[],[f992,f108])).

fof(f992,plain,(
    ! [X0] :
      ( v3_funct_2(k6_partfun1(X0),X0,X0)
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_2(k6_partfun1(X0))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(subsumption_resolution,[],[f991,f77])).

fof(f991,plain,(
    ! [X0] :
      ( v3_funct_2(k6_partfun1(X0),X0,X0)
      | ~ v1_partfun1(k6_partfun1(X0),X0)
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_2(k6_partfun1(X0))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f990,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | v3_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( ( v1_funct_2(X1,X0,X0)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v1_relat_2(X1) )
       => ( v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',cc4_funct_2)).

fof(f567,plain,
    ( ~ spl3_73
    | spl3_7 ),
    inference(avatar_split_clause,[],[f557,f137,f565])).

fof(f137,plain,
    ( spl3_7
  <=> k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f557,plain,
    ( k10_relat_1(k6_partfun1(sK0),sK1) != sK1
    | ~ spl3_7 ),
    inference(superposition,[],[f138,f544])).

fof(f138,plain,
    ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f476,plain,
    ( spl3_70
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f463,f423,f474])).

fof(f474,plain,
    ( spl3_70
  <=> r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f423,plain,
    ( spl3_62
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f463,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_62 ),
    inference(superposition,[],[f141,f424])).

fof(f424,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f423])).

fof(f141,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f90,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',existence_m1_subset_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t3_subset)).

fof(f458,plain,
    ( ~ spl3_69
    | spl3_61
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f442,f423,f410,f456])).

fof(f456,plain,
    ( spl3_69
  <=> k1_xboole_0 != sK2(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f410,plain,
    ( spl3_61
  <=> k1_xboole_0 != sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f442,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0)
    | ~ spl3_61
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f411,f424])).

fof(f411,plain,
    ( k1_xboole_0 != sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f410])).

fof(f451,plain,
    ( ~ spl3_67
    | spl3_59
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f443,f423,f397,f449])).

fof(f449,plain,
    ( spl3_67
  <=> ~ v1_xboole_0(sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f397,plain,
    ( spl3_59
  <=> ~ v1_xboole_0(sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f443,plain,
    ( ~ v1_xboole_0(sK2(k1_xboole_0))
    | ~ spl3_59
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f398,f424])).

fof(f398,plain,
    ( ~ v1_xboole_0(sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f397])).

fof(f441,plain,
    ( spl3_64
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f432,f413,f439])).

fof(f439,plain,
    ( spl3_64
  <=> m1_subset_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f413,plain,
    ( spl3_60
  <=> k1_xboole_0 = sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f432,plain,
    ( m1_subset_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl3_60 ),
    inference(superposition,[],[f82,f414])).

fof(f414,plain,
    ( k1_xboole_0 = sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f413])).

fof(f425,plain,
    ( spl3_62
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f418,f389,f423])).

fof(f389,plain,
    ( spl3_54
  <=> v1_xboole_0(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f418,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl3_54 ),
    inference(resolution,[],[f390,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t6_boole)).

fof(f390,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f389])).

fof(f415,plain,
    ( spl3_60
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f408,f400,f413])).

fof(f400,plain,
    ( spl3_58
  <=> v1_xboole_0(sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f408,plain,
    ( k1_xboole_0 = sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl3_58 ),
    inference(resolution,[],[f401,f79])).

fof(f401,plain,
    ( v1_xboole_0(sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f400])).

fof(f405,plain,(
    ~ spl3_56 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl3_56 ),
    inference(resolution,[],[f395,f82])).

fof(f395,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl3_56
  <=> ! [X0] : ~ m1_subset_1(X0,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f402,plain,
    ( spl3_56
    | spl3_58
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f392,f383,f400,f394])).

fof(f383,plain,
    ( spl3_52
  <=> ! [X5] : ~ r2_hidden(X5,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f392,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
        | ~ m1_subset_1(X0,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl3_52 ),
    inference(resolution,[],[f384,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t2_subset)).

fof(f384,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f383])).

fof(f391,plain,
    ( spl3_52
    | spl3_54
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f347,f115,f389,f383])).

fof(f115,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f347,plain,
    ( ! [X5] :
        ( v1_xboole_0(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r2_hidden(X5,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl3_0 ),
    inference(resolution,[],[f341,f155])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl3_0 ),
    inference(resolution,[],[f98,f116])).

fof(f116,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f115])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t5_subset)).

fof(f341,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK2(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK2(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f258,f82])).

fof(f258,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,sK2(k1_zfmisc_1(X8)))
      | v1_xboole_0(sK2(k1_zfmisc_1(X8)))
      | m1_subset_1(X7,X8) ) ),
    inference(resolution,[],[f158,f82])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f97,f85])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t4_subset)).

fof(f379,plain,
    ( ~ spl3_49
    | spl3_40
    | spl3_50
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f366,f357,f377,f306,f371])).

fof(f371,plain,
    ( spl3_49
  <=> ~ m1_subset_1(sK0,sK2(sK2(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f306,plain,
    ( spl3_40
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f377,plain,
    ( spl3_50
  <=> v1_xboole_0(sK2(sK2(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f357,plain,
    ( spl3_44
  <=> m1_subset_1(sK2(sK2(k1_zfmisc_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f366,plain,
    ( v1_xboole_0(sK2(sK2(k1_zfmisc_1(sK1))))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK2(sK2(k1_zfmisc_1(sK1))))
    | ~ spl3_44 ),
    inference(resolution,[],[f358,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f152,f85])).

fof(f152,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f85,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',antisymmetry_r2_hidden)).

fof(f358,plain,
    ( m1_subset_1(sK2(sK2(k1_zfmisc_1(sK1))),sK0)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f357])).

fof(f365,plain,
    ( spl3_44
    | spl3_46
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f350,f260,f363,f357])).

fof(f363,plain,
    ( spl3_46
  <=> v1_xboole_0(sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f260,plain,
    ( spl3_30
  <=> ! [X6] :
        ( m1_subset_1(X6,sK0)
        | ~ m1_subset_1(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f350,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(sK1)))
    | m1_subset_1(sK2(sK2(k1_zfmisc_1(sK1))),sK0)
    | ~ spl3_30 ),
    inference(resolution,[],[f341,f261])).

fof(f261,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,sK1)
        | m1_subset_1(X6,sK0) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f260])).

fof(f314,plain,
    ( ~ spl3_39
    | spl3_40
    | spl3_42
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f294,f278,f312,f306,f300])).

fof(f300,plain,
    ( spl3_39
  <=> ~ m1_subset_1(sK0,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f312,plain,
    ( spl3_42
  <=> v1_xboole_0(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f278,plain,
    ( spl3_34
  <=> m1_subset_1(sK2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f294,plain,
    ( v1_xboole_0(sK2(sK1))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK2(sK1))
    | ~ spl3_34 ),
    inference(resolution,[],[f279,f154])).

fof(f279,plain,
    ( m1_subset_1(sK2(sK1),sK0)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f278])).

fof(f293,plain,
    ( spl3_36
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f284,f270,f147,f291])).

fof(f291,plain,
    ( spl3_36
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f270,plain,
    ( spl3_32
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f284,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(superposition,[],[f148,f271])).

fof(f271,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f270])).

fof(f280,plain,
    ( spl3_34
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f273,f260,f278])).

fof(f273,plain,
    ( m1_subset_1(sK2(sK1),sK0)
    | ~ spl3_30 ),
    inference(resolution,[],[f261,f82])).

fof(f272,plain,
    ( spl3_32
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f265,f188,f270])).

fof(f188,plain,
    ( spl3_16
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f265,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_16 ),
    inference(resolution,[],[f189,f79])).

fof(f189,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f262,plain,
    ( spl3_16
    | spl3_30
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f257,f129,f260,f188])).

fof(f129,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f257,plain,
    ( ! [X6] :
        ( m1_subset_1(X6,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X6,sK1) )
    | ~ spl3_4 ),
    inference(resolution,[],[f158,f130])).

fof(f130,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f247,plain,
    ( spl3_28
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f215,f208,f245])).

fof(f245,plain,
    ( spl3_28
  <=> k1_xboole_0 = k9_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f208,plain,
    ( spl3_22
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f215,plain,
    ( k1_xboole_0 = k9_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_22 ),
    inference(superposition,[],[f160,f209])).

fof(f209,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f160,plain,(
    ! [X0] : k9_relat_1(k6_partfun1(X0),sK2(k1_zfmisc_1(X0))) = sK2(k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f110,f82])).

fof(f236,plain,
    ( spl3_26
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f218,f208,f234])).

fof(f234,plain,
    ( spl3_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f218,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_22 ),
    inference(superposition,[],[f82,f209])).

fof(f226,plain,
    ( spl3_24
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f216,f208,f224])).

fof(f224,plain,
    ( spl3_24
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f216,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_22 ),
    inference(superposition,[],[f141,f209])).

fof(f212,plain,(
    ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl3_18 ),
    inference(resolution,[],[f193,f82])).

fof(f193,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl3_18
  <=> ! [X0] : ~ m1_subset_1(X0,sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f210,plain,
    ( spl3_22
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f203,f198,f208])).

fof(f198,plain,
    ( spl3_20
  <=> v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f203,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_20 ),
    inference(resolution,[],[f199,f79])).

fof(f199,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl3_18
    | spl3_20
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f157,f115,f198,f192])).

fof(f157,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
        | ~ m1_subset_1(X0,sK2(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl3_0 ),
    inference(resolution,[],[f156,f85])).

fof(f156,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl3_0 ),
    inference(resolution,[],[f155,f82])).

fof(f190,plain,
    ( ~ spl3_13
    | spl3_14
    | spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f169,f129,f188,f182,f176])).

fof(f176,plain,
    ( spl3_13
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f182,plain,
    ( spl3_14
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f169,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f154,f130])).

fof(f168,plain,
    ( spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f159,f129,f166])).

fof(f166,plain,
    ( spl3_10
  <=> k9_relat_1(k6_partfun1(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f159,plain,
    ( k9_relat_1(k6_partfun1(sK0),sK1) = sK1
    | ~ spl3_4 ),
    inference(resolution,[],[f110,f130])).

fof(f149,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f140,f129,f147])).

fof(f140,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f90,f130])).

fof(f139,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f67,f137])).

fof(f67,plain,(
    k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f62])).

fof(f62,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t171_funct_2)).

fof(f131,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f66,f129])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f124,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f69,f122])).

fof(f122,plain,
    ( spl3_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f69,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',d2_xboole_0)).

fof(f117,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f103,f115])).

fof(f103,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f68,f69])).

fof(f68,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
