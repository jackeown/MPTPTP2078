%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t174_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:37 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  294 ( 744 expanded)
%              Number of leaves         :   82 ( 315 expanded)
%              Depth                    :   10
%              Number of atoms          :  690 (1664 expanded)
%              Number of equality atoms :   80 ( 204 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f858,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f104,f111,f118,f126,f146,f156,f167,f185,f192,f206,f221,f229,f248,f261,f268,f276,f290,f298,f312,f326,f337,f347,f356,f363,f421,f439,f446,f453,f460,f469,f476,f495,f509,f529,f544,f548,f560,f574,f581,f601,f602,f610,f630,f680,f687,f696,f703,f712,f719,f768,f841,f857])).

fof(f857,plain,
    ( ~ spl4_0
    | spl4_9
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f856])).

fof(f856,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_9
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f853,f125])).

fof(f125,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_9
  <=> k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f853,plain,
    ( k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(superposition,[],[f847,f297])).

fof(f297,plain,
    ( k9_relat_1(k6_partfun1(sK1),sK2) = sK2
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl4_38
  <=> k9_relat_1(k6_partfun1(sK1),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f847,plain,
    ( ! [X12,X11] : k9_relat_1(k7_relat_1(sK0,X11),X12) = k9_relat_1(sK0,k9_relat_1(k6_partfun1(X11),X12))
    | ~ spl4_0 ),
    inference(forward_demodulation,[],[f845,f252])).

fof(f252,plain,
    ( ! [X8] : k7_relat_1(sK0,X8) = k5_relat_1(k6_partfun1(X8),sK0)
    | ~ spl4_0 ),
    inference(resolution,[],[f89,f96])).

fof(f96,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t94_relat_1)).

fof(f845,plain,
    ( ! [X12,X11] : k9_relat_1(k5_relat_1(k6_partfun1(X11),sK0),X12) = k9_relat_1(sK0,k9_relat_1(k6_partfun1(X11),X12))
    | ~ spl4_0 ),
    inference(resolution,[],[f424,f96])).

fof(f424,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_relat_1(X8)
      | k9_relat_1(X8,k9_relat_1(k6_partfun1(X9),X10)) = k9_relat_1(k5_relat_1(k6_partfun1(X9),X8),X10) ) ),
    inference(resolution,[],[f73,f87])).

fof(f87,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f65,f66])).

fof(f65,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',dt_k6_relat_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t159_relat_1)).

fof(f841,plain,
    ( spl4_92
    | spl4_104
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f591,f527,f839,f672])).

fof(f672,plain,
    ( spl4_92
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f839,plain,
    ( spl4_104
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f527,plain,
    ( spl4_76
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f591,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl4_76 ),
    inference(superposition,[],[f135,f528])).

fof(f528,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f527])).

fof(f135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f82,f128])).

fof(f128,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',existence_m1_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t2_subset)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t4_subset)).

fof(f768,plain,
    ( spl4_84
    | spl4_72
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f562,f542,f493,f579])).

fof(f579,plain,
    ( spl4_84
  <=> r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f493,plain,
    ( spl4_72
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f542,plain,
    ( spl4_78
  <=> m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f562,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_78 ),
    inference(resolution,[],[f543,f76])).

fof(f543,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f542])).

fof(f719,plain,
    ( ~ spl4_103
    | spl4_99 ),
    inference(avatar_split_clause,[],[f705,f701,f717])).

fof(f717,plain,
    ( spl4_103
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).

fof(f701,plain,
    ( spl4_99
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f705,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_99 ),
    inference(resolution,[],[f702,f75])).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t1_subset)).

fof(f702,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f701])).

fof(f712,plain,
    ( ~ spl4_101
    | spl4_99 ),
    inference(avatar_split_clause,[],[f704,f701,f710])).

fof(f710,plain,
    ( spl4_101
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).

fof(f704,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl4_99 ),
    inference(resolution,[],[f702,f79])).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t3_subset)).

fof(f703,plain,
    ( ~ spl4_99
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f695,f685,f154,f144,f701])).

fof(f144,plain,
    ( spl4_10
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f154,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f685,plain,
    ( spl4_96
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f695,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f690,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f690,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_10
    | ~ spl4_96 ),
    inference(resolution,[],[f686,f147])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl4_10 ),
    inference(resolution,[],[f145,f83])).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t5_subset)).

fof(f145,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f686,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f685])).

fof(f696,plain,
    ( ~ spl4_93
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f694,f685,f669])).

fof(f669,plain,
    ( spl4_93
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f694,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_96 ),
    inference(resolution,[],[f686,f81])).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t7_boole)).

fof(f687,plain,
    ( spl4_96
    | spl4_92
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f587,f558,f672,f685])).

fof(f558,plain,
    ( spl4_80
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f587,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_80 ),
    inference(resolution,[],[f559,f76])).

fof(f559,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f558])).

fof(f680,plain,
    ( spl4_92
    | ~ spl4_95
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f592,f527,f678,f672])).

fof(f678,plain,
    ( spl4_95
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f592,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_76 ),
    inference(superposition,[],[f132,f528])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f128,f74])).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',antisymmetry_r2_hidden)).

fof(f630,plain,
    ( spl4_90
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f622,f296,f628])).

fof(f628,plain,
    ( spl4_90
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f622,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl4_38 ),
    inference(superposition,[],[f612,f297])).

fof(f612,plain,(
    ! [X0,X1] : m1_subset_1(k9_relat_1(k6_partfun1(X0),X1),k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f611,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',dt_k6_partfun1)).

fof(f611,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_relat_1(k6_partfun1(X0),X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f84,f519])).

fof(f519,plain,(
    ! [X8,X9] : k9_relat_1(k6_partfun1(X8),X9) = k7_relset_1(X8,X8,k6_partfun1(X8),X9) ),
    inference(resolution,[],[f85,f68])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',redefinition_k7_relset_1)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',dt_k7_relset_1)).

fof(f610,plain,
    ( spl4_88
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f586,f558,f608])).

fof(f608,plain,
    ( spl4_88
  <=> k9_relat_1(k6_partfun1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f586,plain,
    ( k9_relat_1(k6_partfun1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = k1_xboole_0
    | ~ spl4_80 ),
    inference(resolution,[],[f559,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(forward_demodulation,[],[f77,f66])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t162_funct_1)).

fof(f602,plain,
    ( spl4_26
    | ~ spl4_76
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f589,f542,f527,f227])).

fof(f227,plain,
    ( spl4_26
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f589,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_76
    | ~ spl4_78 ),
    inference(superposition,[],[f543,f528])).

fof(f601,plain,
    ( ~ spl4_87
    | ~ spl4_76
    | spl4_83 ),
    inference(avatar_split_clause,[],[f588,f572,f527,f599])).

fof(f599,plain,
    ( spl4_87
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f572,plain,
    ( spl4_83
  <=> ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f588,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl4_76
    | ~ spl4_83 ),
    inference(superposition,[],[f573,f528])).

fof(f573,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl4_83 ),
    inference(avatar_component_clause,[],[f572])).

fof(f581,plain,
    ( spl4_84
    | spl4_73
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f537,f507,f490,f579])).

fof(f490,plain,
    ( spl4_73
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f507,plain,
    ( spl4_74
  <=> k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f537,plain,
    ( r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_73
    | ~ spl4_74 ),
    inference(subsumption_resolution,[],[f533,f491])).

fof(f491,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f490])).

fof(f533,plain,
    ( r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_74 ),
    inference(superposition,[],[f128,f508])).

fof(f508,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f507])).

fof(f574,plain,
    ( ~ spl4_83
    | spl4_73
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f536,f507,f490,f572])).

fof(f536,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl4_73
    | ~ spl4_74 ),
    inference(subsumption_resolution,[],[f532,f491])).

fof(f532,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_74 ),
    inference(superposition,[],[f132,f508])).

fof(f560,plain,
    ( spl4_80
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f553,f527,f558])).

fof(f553,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_76 ),
    inference(superposition,[],[f70,f528])).

fof(f548,plain,
    ( ~ spl4_35
    | spl4_75
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f545,f527,f504,f271])).

fof(f271,plain,
    ( spl4_35
  <=> k1_xboole_0 != sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f504,plain,
    ( spl4_75
  <=> k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f545,plain,
    ( k1_xboole_0 != sK3(k1_xboole_0)
    | ~ spl4_75
    | ~ spl4_76 ),
    inference(forward_demodulation,[],[f505,f528])).

fof(f505,plain,
    ( k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f504])).

fof(f544,plain,
    ( spl4_78
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f534,f507,f542])).

fof(f534,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_74 ),
    inference(superposition,[],[f70,f508])).

fof(f529,plain,
    ( spl4_76
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f514,f493,f154,f144,f527])).

fof(f514,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f510,f155])).

fof(f510,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_10
    | ~ spl4_72 ),
    inference(resolution,[],[f494,f148])).

fof(f148,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl4_10 ),
    inference(resolution,[],[f145,f80])).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t8_boole)).

fof(f494,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f493])).

fof(f509,plain,
    ( spl4_74
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f500,f487,f154,f144,f507])).

fof(f487,plain,
    ( spl4_70
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f500,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f496,f155])).

fof(f496,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_10
    | ~ spl4_70 ),
    inference(resolution,[],[f488,f148])).

fof(f488,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f487])).

fof(f495,plain,
    ( spl4_70
    | spl4_72
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f384,f102,f493,f487])).

fof(f102,plain,
    ( spl4_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f384,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_2 ),
    inference(resolution,[],[f372,f70])).

fof(f372,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK3(X2)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f135,f136])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f134,f128])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f83,f103])).

fof(f103,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f476,plain,
    ( ~ spl4_69
    | spl4_65 ),
    inference(avatar_split_clause,[],[f462,f458,f474])).

fof(f474,plain,
    ( spl4_69
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f458,plain,
    ( spl4_65
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f462,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_65 ),
    inference(resolution,[],[f459,f75])).

fof(f459,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f458])).

fof(f469,plain,
    ( ~ spl4_67
    | spl4_65 ),
    inference(avatar_split_clause,[],[f461,f458,f467])).

fof(f467,plain,
    ( spl4_67
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f461,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_65 ),
    inference(resolution,[],[f459,f79])).

fof(f460,plain,
    ( ~ spl4_65
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f445,f413,f154,f144,f458])).

fof(f413,plain,
    ( spl4_56
  <=> r2_hidden(sK3(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f445,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f440,f155])).

fof(f440,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_10
    | ~ spl4_56 ),
    inference(resolution,[],[f414,f147])).

fof(f414,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f413])).

fof(f453,plain,
    ( ~ spl4_63
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f443,f413,f451])).

fof(f451,plain,
    ( spl4_63
  <=> ~ r2_hidden(sK1,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f443,plain,
    ( ~ r2_hidden(sK1,sK3(sK2))
    | ~ spl4_56 ),
    inference(resolution,[],[f414,f74])).

fof(f446,plain,
    ( ~ spl4_59
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f444,f413,f416])).

fof(f416,plain,
    ( spl4_59
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f444,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_56 ),
    inference(resolution,[],[f414,f81])).

fof(f439,plain,
    ( spl4_60
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f430,f407,f154,f144,f437])).

fof(f437,plain,
    ( spl4_60
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f407,plain,
    ( spl4_54
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f430,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f426,f155])).

fof(f426,plain,
    ( sK2 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_54 ),
    inference(resolution,[],[f408,f148])).

fof(f408,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f407])).

fof(f421,plain,
    ( spl4_54
    | spl4_56
    | spl4_58
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f402,f109,f419,f413,f407])).

fof(f419,plain,
    ( spl4_58
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f109,plain,
    ( spl4_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f402,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK3(sK2),sK1)
    | v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f394,f110])).

fof(f110,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f394,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(sK3(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f371,f79])).

fof(f371,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | r2_hidden(sK3(X0),X1) ) ),
    inference(resolution,[],[f135,f76])).

fof(f363,plain,
    ( ~ spl4_53
    | spl4_49 ),
    inference(avatar_split_clause,[],[f349,f345,f361])).

fof(f361,plain,
    ( spl4_53
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f345,plain,
    ( spl4_49
  <=> ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f349,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_49 ),
    inference(resolution,[],[f346,f75])).

fof(f346,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f345])).

fof(f356,plain,
    ( ~ spl4_51
    | spl4_49 ),
    inference(avatar_split_clause,[],[f348,f345,f354])).

fof(f354,plain,
    ( spl4_51
  <=> ~ r1_tarski(k1_zfmisc_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f348,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_xboole_0)
    | ~ spl4_49 ),
    inference(resolution,[],[f346,f79])).

fof(f347,plain,
    ( ~ spl4_49
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f327,f310,f102,f345])).

fof(f310,plain,
    ( spl4_42
  <=> r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f327,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(resolution,[],[f311,f134])).

fof(f311,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f310])).

fof(f337,plain,
    ( ~ spl4_47
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f329,f310,f335])).

fof(f335,plain,
    ( spl4_47
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f329,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),sK2)
    | ~ spl4_42 ),
    inference(resolution,[],[f311,f74])).

fof(f326,plain,
    ( spl4_44
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f317,f304,f154,f144,f324])).

fof(f324,plain,
    ( spl4_44
  <=> k1_xboole_0 = k1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f304,plain,
    ( spl4_40
  <=> v1_xboole_0(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f317,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK1)
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f313,f155])).

fof(f313,plain,
    ( k1_zfmisc_1(sK1) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_40 ),
    inference(resolution,[],[f305,f148])).

fof(f305,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f304])).

fof(f312,plain,
    ( spl4_40
    | spl4_42
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f299,f109,f310,f304])).

fof(f299,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f130,f110])).

fof(f130,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,X3)
      | r2_hidden(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f76,f79])).

fof(f298,plain,
    ( spl4_38
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f291,f109,f296])).

fof(f291,plain,
    ( k9_relat_1(k6_partfun1(sK1),sK2) = sK2
    | ~ spl4_4 ),
    inference(resolution,[],[f279,f110])).

fof(f279,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(resolution,[],[f90,f79])).

fof(f290,plain,
    ( spl4_36
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f281,f165,f288])).

fof(f288,plain,
    ( spl4_36
  <=> k9_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f165,plain,
    ( spl4_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f281,plain,
    ( k9_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ spl4_14 ),
    inference(resolution,[],[f90,f166])).

fof(f166,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f276,plain,
    ( spl4_34
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f234,f219,f154,f144,f274])).

fof(f274,plain,
    ( spl4_34
  <=> k1_xboole_0 = sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f219,plain,
    ( spl4_24
  <=> v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f234,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f230,f155])).

fof(f230,plain,
    ( sK3(k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(resolution,[],[f220,f148])).

fof(f220,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f268,plain,
    ( ~ spl4_33
    | spl4_29 ),
    inference(avatar_split_clause,[],[f254,f246,f266])).

fof(f266,plain,
    ( spl4_33
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f246,plain,
    ( spl4_29
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f254,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_29 ),
    inference(resolution,[],[f247,f75])).

fof(f247,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f246])).

fof(f261,plain,
    ( ~ spl4_31
    | spl4_29 ),
    inference(avatar_split_clause,[],[f253,f246,f259])).

fof(f259,plain,
    ( spl4_31
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f253,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_29 ),
    inference(resolution,[],[f247,f79])).

fof(f248,plain,
    ( ~ spl4_29
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f238,f190,f102,f246])).

fof(f190,plain,
    ( spl4_20
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f238,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(resolution,[],[f191,f134])).

fof(f191,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f229,plain,
    ( spl4_26
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f211,f204,f165,f227])).

fof(f204,plain,
    ( spl4_22
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f211,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(superposition,[],[f166,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f221,plain,
    ( spl4_24
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f209,f204,f144,f219])).

fof(f209,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(superposition,[],[f145,f205])).

fof(f206,plain,
    ( spl4_22
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f197,f177,f154,f144,f204])).

fof(f177,plain,
    ( spl4_16
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f197,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f193,f155])).

fof(f193,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(resolution,[],[f178,f148])).

fof(f178,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f192,plain,
    ( spl4_16
    | spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f159,f154,f190,f177])).

fof(f159,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(superposition,[],[f128,f155])).

fof(f185,plain,
    ( spl4_16
    | ~ spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f158,f154,f183,f177])).

fof(f183,plain,
    ( spl4_19
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f158,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(superposition,[],[f132,f155])).

fof(f167,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f160,f154,f165])).

fof(f160,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(superposition,[],[f70,f155])).

fof(f156,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f149,f144,f154])).

fof(f149,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10 ),
    inference(resolution,[],[f145,f69])).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t6_boole)).

fof(f146,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f137,f102,f144])).

fof(f137,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f136,f70])).

fof(f126,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f62,f124])).

fof(f62,plain,(
    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(sK2,sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(X2,X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
     => ( k9_relat_1(X0,sK2) != k9_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(sK2,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X2,X1)
         => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',t174_funct_2)).

fof(f118,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f64,f116])).

fof(f116,plain,
    ( spl4_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f64,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',d2_xboole_0)).

fof(f111,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f61,f109])).

fof(f61,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f86,f102])).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f63,f64])).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t174_funct_2.p',dt_o_0_0_xboole_0)).

fof(f97,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f60,f95])).

fof(f60,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
