%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t175_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:37 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  303 ( 784 expanded)
%              Number of leaves         :   85 ( 327 expanded)
%              Depth                    :   10
%              Number of atoms          :  706 (1731 expanded)
%              Number of equality atoms :   90 ( 240 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1049,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f103,f110,f117,f125,f145,f155,f166,f184,f191,f205,f220,f228,f247,f260,f267,f275,f291,f305,f316,f325,f332,f339,f353,f372,f415,f429,f441,f448,f455,f464,f471,f489,f556,f570,f584,f599,f603,f615,f629,f636,f664,f677,f684,f693,f700,f709,f716,f747,f754,f768,f859,f1017,f1042,f1044])).

fof(f1044,plain,
    ( ~ spl4_0
    | spl4_9
    | ~ spl4_104 ),
    inference(avatar_contradiction_clause,[],[f1043])).

fof(f1043,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_9
    | ~ spl4_104 ),
    inference(subsumption_resolution,[],[f1026,f124])).

fof(f124,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_9
  <=> k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1026,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl4_0
    | ~ spl4_104 ),
    inference(superposition,[],[f753,f1023])).

fof(f1023,plain,
    ( ! [X12,X11] : k10_relat_1(k7_relat_1(sK0,X11),X12) = k10_relat_1(k6_partfun1(X11),k10_relat_1(sK0,X12))
    | ~ spl4_0 ),
    inference(forward_demodulation,[],[f1021,f251])).

fof(f251,plain,
    ( ! [X8] : k7_relat_1(sK0,X8) = k5_relat_1(k6_partfun1(X8),sK0)
    | ~ spl4_0 ),
    inference(resolution,[],[f89,f95])).

fof(f95,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(forward_demodulation,[],[f72,f66])).

fof(f66,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',redefinition_k6_partfun1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t94_relat_1)).

fof(f1021,plain,
    ( ! [X12,X11] : k10_relat_1(k5_relat_1(k6_partfun1(X11),sK0),X12) = k10_relat_1(k6_partfun1(X11),k10_relat_1(sK0,X12))
    | ~ spl4_0 ),
    inference(resolution,[],[f538,f95])).

fof(f538,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_relat_1(X8)
      | k10_relat_1(k5_relat_1(k6_partfun1(X9),X8),X10) = k10_relat_1(k6_partfun1(X9),k10_relat_1(X8,X10)) ) ),
    inference(resolution,[],[f73,f87])).

fof(f87,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f65,f66])).

fof(f65,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',dt_k6_relat_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t181_relat_1)).

fof(f753,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_partfun1(sK1),k10_relat_1(sK0,sK2))
    | ~ spl4_104 ),
    inference(avatar_component_clause,[],[f752])).

fof(f752,plain,
    ( spl4_104
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_partfun1(sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f1042,plain,
    ( ~ spl4_0
    | spl4_9
    | ~ spl4_104 ),
    inference(avatar_contradiction_clause,[],[f1041])).

fof(f1041,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_9
    | ~ spl4_104 ),
    inference(subsumption_resolution,[],[f1024,f124])).

fof(f1024,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl4_0
    | ~ spl4_104 ),
    inference(superposition,[],[f1023,f753])).

fof(f1017,plain,
    ( spl4_90
    | spl4_110
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f654,f582,f1015,f669])).

fof(f669,plain,
    ( spl4_90
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f1015,plain,
    ( spl4_110
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f582,plain,
    ( spl4_78
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f654,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl4_78 ),
    inference(superposition,[],[f134,f583])).

fof(f583,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f582])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f82,f127])).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f76,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',existence_m1_subset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t2_subset)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t4_subset)).

fof(f859,plain,
    ( spl4_108
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f642,f613,f857])).

fof(f857,plain,
    ( spl4_108
  <=> k1_xboole_0 = k8_relset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f613,plain,
    ( spl4_82
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f642,plain,
    ( k1_xboole_0 = k8_relset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl4_82 ),
    inference(resolution,[],[f614,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t171_funct_2)).

fof(f614,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f613])).

fof(f768,plain,
    ( spl4_106
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f758,f582,f766])).

fof(f766,plain,
    ( spl4_106
  <=> k10_relat_1(k6_partfun1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f758,plain,
    ( k10_relat_1(k6_partfun1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = k1_xboole_0
    | ~ spl4_78 ),
    inference(superposition,[],[f722,f583])).

fof(f722,plain,(
    ! [X1] : k10_relat_1(k6_partfun1(X1),sK3(k1_zfmisc_1(X1))) = sK3(k1_zfmisc_1(X1)) ),
    inference(superposition,[],[f646,f344])).

fof(f344,plain,(
    ! [X5] : k8_relset_1(X5,X5,k6_partfun1(X5),sK3(k1_zfmisc_1(X5))) = sK3(k1_zfmisc_1(X5)) ),
    inference(resolution,[],[f77,f70])).

fof(f646,plain,(
    ! [X8,X9] : k10_relat_1(k6_partfun1(X8),X9) = k8_relset_1(X8,X8,k6_partfun1(X8),X9) ),
    inference(resolution,[],[f85,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',dt_k6_partfun1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',redefinition_k8_relset_1)).

fof(f754,plain,
    ( spl4_104
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f721,f370,f752])).

fof(f370,plain,
    ( spl4_52
  <=> k10_relat_1(sK0,sK2) = k8_relset_1(sK1,sK1,k6_partfun1(sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f721,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_partfun1(sK1),k10_relat_1(sK0,sK2))
    | ~ spl4_52 ),
    inference(superposition,[],[f646,f371])).

fof(f371,plain,
    ( k10_relat_1(sK0,sK2) = k8_relset_1(sK1,sK1,k6_partfun1(sK1),k10_relat_1(sK0,sK2))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f370])).

fof(f747,plain,
    ( spl4_102
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f719,f351,f745])).

fof(f745,plain,
    ( spl4_102
  <=> k10_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f351,plain,
    ( spl4_50
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f719,plain,
    ( k10_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ spl4_50 ),
    inference(superposition,[],[f646,f352])).

fof(f352,plain,
    ( k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f351])).

fof(f716,plain,
    ( ~ spl4_101
    | spl4_97 ),
    inference(avatar_split_clause,[],[f702,f698,f714])).

fof(f714,plain,
    ( spl4_101
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).

fof(f698,plain,
    ( spl4_97
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f702,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_97 ),
    inference(resolution,[],[f699,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t1_subset)).

fof(f699,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_97 ),
    inference(avatar_component_clause,[],[f698])).

fof(f709,plain,
    ( ~ spl4_99
    | spl4_97 ),
    inference(avatar_split_clause,[],[f701,f698,f707])).

fof(f707,plain,
    ( spl4_99
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f701,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl4_97 ),
    inference(resolution,[],[f699,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t3_subset)).

fof(f700,plain,
    ( ~ spl4_97
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f692,f682,f153,f143,f698])).

fof(f143,plain,
    ( spl4_10
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f153,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f682,plain,
    ( spl4_94
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f692,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_94 ),
    inference(forward_demodulation,[],[f687,f154])).

fof(f154,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f687,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_10
    | ~ spl4_94 ),
    inference(resolution,[],[f683,f146])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl4_10 ),
    inference(resolution,[],[f144,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t5_subset)).

fof(f144,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f683,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f682])).

fof(f693,plain,
    ( ~ spl4_91
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f691,f682,f666])).

fof(f666,plain,
    ( spl4_91
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f691,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_94 ),
    inference(resolution,[],[f683,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t7_boole)).

fof(f684,plain,
    ( spl4_94
    | spl4_90
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f643,f613,f669,f682])).

fof(f643,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_82 ),
    inference(resolution,[],[f614,f76])).

fof(f677,plain,
    ( spl4_90
    | ~ spl4_93
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f655,f582,f675,f669])).

fof(f675,plain,
    ( spl4_93
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f655,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_78 ),
    inference(superposition,[],[f131,f583])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f127,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',antisymmetry_r2_hidden)).

fof(f664,plain,
    ( ~ spl4_89
    | ~ spl4_78
    | spl4_85 ),
    inference(avatar_split_clause,[],[f652,f627,f582,f662])).

fof(f662,plain,
    ( spl4_89
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f627,plain,
    ( spl4_85
  <=> ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f652,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl4_78
    | ~ spl4_85 ),
    inference(superposition,[],[f628,f583])).

fof(f628,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl4_85 ),
    inference(avatar_component_clause,[],[f627])).

fof(f636,plain,
    ( spl4_86
    | spl4_75
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f592,f568,f551,f634])).

fof(f634,plain,
    ( spl4_86
  <=> r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f551,plain,
    ( spl4_75
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f568,plain,
    ( spl4_76
  <=> k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f592,plain,
    ( r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_75
    | ~ spl4_76 ),
    inference(subsumption_resolution,[],[f588,f552])).

fof(f552,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f551])).

fof(f588,plain,
    ( r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_76 ),
    inference(superposition,[],[f127,f569])).

fof(f569,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f568])).

fof(f629,plain,
    ( ~ spl4_85
    | spl4_75
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f591,f568,f551,f627])).

fof(f591,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl4_75
    | ~ spl4_76 ),
    inference(subsumption_resolution,[],[f587,f552])).

fof(f587,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_76 ),
    inference(superposition,[],[f131,f569])).

fof(f615,plain,
    ( spl4_82
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f608,f582,f613])).

fof(f608,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_78 ),
    inference(superposition,[],[f70,f583])).

fof(f603,plain,
    ( ~ spl4_35
    | spl4_77
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f600,f582,f565,f270])).

fof(f270,plain,
    ( spl4_35
  <=> k1_xboole_0 != sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f565,plain,
    ( spl4_77
  <=> k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f600,plain,
    ( k1_xboole_0 != sK3(k1_xboole_0)
    | ~ spl4_77
    | ~ spl4_78 ),
    inference(forward_demodulation,[],[f566,f583])).

fof(f566,plain,
    ( k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f565])).

fof(f599,plain,
    ( spl4_80
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f589,f568,f597])).

fof(f597,plain,
    ( spl4_80
  <=> m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f589,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_76 ),
    inference(superposition,[],[f70,f569])).

fof(f584,plain,
    ( spl4_78
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f575,f554,f153,f143,f582])).

fof(f554,plain,
    ( spl4_74
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f575,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_74 ),
    inference(forward_demodulation,[],[f571,f154])).

fof(f571,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_10
    | ~ spl4_74 ),
    inference(resolution,[],[f555,f147])).

fof(f147,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl4_10 ),
    inference(resolution,[],[f144,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t8_boole)).

fof(f555,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f554])).

fof(f570,plain,
    ( spl4_76
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f561,f548,f153,f143,f568])).

fof(f548,plain,
    ( spl4_72
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f561,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f557,f154])).

fof(f557,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_10
    | ~ spl4_72 ),
    inference(resolution,[],[f549,f147])).

fof(f549,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f548])).

fof(f556,plain,
    ( spl4_72
    | spl4_74
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f375,f101,f554,f548])).

fof(f101,plain,
    ( spl4_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f375,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_2 ),
    inference(resolution,[],[f356,f70])).

fof(f356,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK3(X2)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f134,f135])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f133,f127])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f83,f102])).

fof(f102,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f489,plain,
    ( spl4_70
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f481,f370,f487])).

fof(f487,plain,
    ( spl4_70
  <=> m1_subset_1(k10_relat_1(sK0,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f481,plain,
    ( m1_subset_1(k10_relat_1(sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_52 ),
    inference(superposition,[],[f432,f371])).

fof(f432,plain,(
    ! [X8,X9] : m1_subset_1(k8_relset_1(X8,X8,k6_partfun1(X8),X9),k1_zfmisc_1(X8)) ),
    inference(resolution,[],[f84,f68])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',dt_k8_relset_1)).

fof(f471,plain,
    ( ~ spl4_69
    | spl4_65 ),
    inference(avatar_split_clause,[],[f457,f453,f469])).

fof(f469,plain,
    ( spl4_69
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f453,plain,
    ( spl4_65
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f457,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_65 ),
    inference(resolution,[],[f454,f75])).

fof(f454,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f453])).

fof(f464,plain,
    ( ~ spl4_67
    | spl4_65 ),
    inference(avatar_split_clause,[],[f456,f453,f462])).

fof(f462,plain,
    ( spl4_67
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f456,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_65 ),
    inference(resolution,[],[f454,f79])).

fof(f455,plain,
    ( ~ spl4_65
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f440,f407,f153,f143,f453])).

fof(f407,plain,
    ( spl4_56
  <=> r2_hidden(sK3(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f440,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f435,f154])).

fof(f435,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_10
    | ~ spl4_56 ),
    inference(resolution,[],[f408,f146])).

fof(f408,plain,
    ( r2_hidden(sK3(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f407])).

fof(f448,plain,
    ( ~ spl4_63
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f438,f407,f446])).

fof(f446,plain,
    ( spl4_63
  <=> ~ r2_hidden(sK1,sK3(k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f438,plain,
    ( ~ r2_hidden(sK1,sK3(k10_relat_1(sK0,sK2)))
    | ~ spl4_56 ),
    inference(resolution,[],[f408,f74])).

fof(f441,plain,
    ( ~ spl4_59
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f439,f407,f410])).

fof(f410,plain,
    ( spl4_59
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f439,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_56 ),
    inference(resolution,[],[f408,f81])).

fof(f429,plain,
    ( spl4_60
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f420,f401,f153,f143,f427])).

fof(f427,plain,
    ( spl4_60
  <=> k10_relat_1(sK0,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f401,plain,
    ( spl4_54
  <=> v1_xboole_0(k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f420,plain,
    ( k10_relat_1(sK0,sK2) = k1_xboole_0
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f416,f154])).

fof(f416,plain,
    ( k10_relat_1(sK0,sK2) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_54 ),
    inference(resolution,[],[f402,f147])).

fof(f402,plain,
    ( v1_xboole_0(k10_relat_1(sK0,sK2))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f401])).

fof(f415,plain,
    ( spl4_54
    | spl4_56
    | spl4_58
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f396,f115,f413,f407,f401])).

fof(f413,plain,
    ( spl4_58
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f115,plain,
    ( spl4_6
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f396,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK3(k10_relat_1(sK0,sK2)),sK1)
    | v1_xboole_0(k10_relat_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f389,f116])).

fof(f116,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f389,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(sK3(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f355,f79])).

fof(f355,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | r2_hidden(sK3(X0),X1) ) ),
    inference(resolution,[],[f134,f76])).

fof(f372,plain,
    ( spl4_52
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f365,f115,f370])).

fof(f365,plain,
    ( k10_relat_1(sK0,sK2) = k8_relset_1(sK1,sK1,k6_partfun1(sK1),k10_relat_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f340,f116])).

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(resolution,[],[f77,f79])).

fof(f353,plain,
    ( spl4_50
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f342,f164,f351])).

fof(f164,plain,
    ( spl4_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f342,plain,
    ( k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_14 ),
    inference(resolution,[],[f77,f165])).

fof(f165,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f339,plain,
    ( ~ spl4_49
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f308,f289,f337])).

fof(f337,plain,
    ( spl4_49
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f289,plain,
    ( spl4_38
  <=> r2_hidden(k10_relat_1(sK0,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f308,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),k10_relat_1(sK0,sK2))
    | ~ spl4_38 ),
    inference(resolution,[],[f290,f74])).

fof(f290,plain,
    ( r2_hidden(k10_relat_1(sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f289])).

fof(f332,plain,
    ( ~ spl4_47
    | spl4_43 ),
    inference(avatar_split_clause,[],[f318,f314,f330])).

fof(f330,plain,
    ( spl4_47
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f314,plain,
    ( spl4_43
  <=> ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f318,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_43 ),
    inference(resolution,[],[f315,f75])).

fof(f315,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f314])).

fof(f325,plain,
    ( ~ spl4_45
    | spl4_43 ),
    inference(avatar_split_clause,[],[f317,f314,f323])).

fof(f323,plain,
    ( spl4_45
  <=> ~ r1_tarski(k1_zfmisc_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f317,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_xboole_0)
    | ~ spl4_43 ),
    inference(resolution,[],[f315,f79])).

fof(f316,plain,
    ( ~ spl4_43
    | ~ spl4_2
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f306,f289,f101,f314])).

fof(f306,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_38 ),
    inference(resolution,[],[f290,f133])).

fof(f305,plain,
    ( spl4_40
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f296,f283,f153,f143,f303])).

fof(f303,plain,
    ( spl4_40
  <=> k1_xboole_0 = k1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f283,plain,
    ( spl4_36
  <=> v1_xboole_0(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f296,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK1)
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f292,f154])).

fof(f292,plain,
    ( k1_zfmisc_1(sK1) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_36 ),
    inference(resolution,[],[f284,f147])).

fof(f284,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f283])).

fof(f291,plain,
    ( spl4_36
    | spl4_38
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f278,f115,f289,f283])).

fof(f278,plain,
    ( r2_hidden(k10_relat_1(sK0,sK2),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f129,f116])).

fof(f129,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,X3)
      | r2_hidden(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f76,f79])).

fof(f275,plain,
    ( spl4_34
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f233,f218,f153,f143,f273])).

fof(f273,plain,
    ( spl4_34
  <=> k1_xboole_0 = sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f218,plain,
    ( spl4_24
  <=> v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f233,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f229,f154])).

fof(f229,plain,
    ( sK3(k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(resolution,[],[f219,f147])).

fof(f219,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f218])).

fof(f267,plain,
    ( ~ spl4_33
    | spl4_29 ),
    inference(avatar_split_clause,[],[f253,f245,f265])).

fof(f265,plain,
    ( spl4_33
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f245,plain,
    ( spl4_29
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f253,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_29 ),
    inference(resolution,[],[f246,f75])).

fof(f246,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f245])).

fof(f260,plain,
    ( ~ spl4_31
    | spl4_29 ),
    inference(avatar_split_clause,[],[f252,f245,f258])).

fof(f258,plain,
    ( spl4_31
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f252,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_29 ),
    inference(resolution,[],[f246,f79])).

fof(f247,plain,
    ( ~ spl4_29
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f237,f189,f101,f245])).

fof(f189,plain,
    ( spl4_20
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f237,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(resolution,[],[f190,f133])).

fof(f190,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f228,plain,
    ( spl4_26
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f210,f203,f164,f226])).

fof(f226,plain,
    ( spl4_26
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f203,plain,
    ( spl4_22
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f210,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(superposition,[],[f165,f204])).

fof(f204,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f220,plain,
    ( spl4_24
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f208,f203,f143,f218])).

fof(f208,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(superposition,[],[f144,f204])).

fof(f205,plain,
    ( spl4_22
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f196,f176,f153,f143,f203])).

fof(f176,plain,
    ( spl4_16
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f196,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f192,f154])).

fof(f192,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(resolution,[],[f177,f147])).

fof(f177,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f191,plain,
    ( spl4_16
    | spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f158,f153,f189,f176])).

fof(f158,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(superposition,[],[f127,f154])).

fof(f184,plain,
    ( spl4_16
    | ~ spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f157,f153,f182,f176])).

fof(f182,plain,
    ( spl4_19
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f157,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(superposition,[],[f131,f154])).

fof(f166,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f159,f153,f164])).

fof(f159,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(superposition,[],[f70,f154])).

fof(f155,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f148,f143,f153])).

fof(f148,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10 ),
    inference(resolution,[],[f144,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t6_boole)).

fof(f145,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f136,f101,f143])).

fof(f136,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f135,f70])).

fof(f125,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f62,f123])).

fof(f62,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',t175_funct_2)).

fof(f117,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f61,f115])).

fof(f61,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f110,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f64,f108])).

fof(f108,plain,
    ( spl4_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f64,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',d2_xboole_0)).

fof(f103,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f86,f101])).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f63,f64])).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t175_funct_2.p',dt_o_0_0_xboole_0)).

fof(f96,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f60,f94])).

fof(f60,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
