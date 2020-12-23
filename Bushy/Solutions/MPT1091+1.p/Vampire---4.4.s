%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t25_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 709 expanded)
%              Number of leaves         :   66 ( 277 expanded)
%              Depth                    :   10
%              Number of atoms          :  643 (1696 expanded)
%              Number of equality atoms :   14 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f100,f113,f121,f125,f132,f151,f167,f176,f188,f193,f206,f214,f218,f221,f228,f230,f237,f244,f265,f291,f294,f306,f323,f333,f344,f363,f370,f375,f382,f391,f401,f412,f416,f417,f429,f431,f439,f448,f455,f465,f479,f491,f496])).

fof(f496,plain,
    ( ~ spl4_4
    | spl4_7
    | ~ spl4_70 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f494,f106])).

fof(f106,plain,
    ( v1_finset_1(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_4
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f494,plain,
    ( ~ v1_finset_1(sK0)
    | ~ spl4_7
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f492,f109])).

fof(f109,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_7
  <=> ~ v1_finset_1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f492,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0)
    | ~ spl4_70 ),
    inference(resolution,[],[f490,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_finset_1(sK2(X0))
      | v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',l22_finset_1)).

fof(f490,plain,
    ( v1_finset_1(sK2(sK0))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl4_70
  <=> v1_finset_1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f491,plain,
    ( spl4_70
    | ~ spl4_4
    | spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f484,f123,f108,f105,f489])).

fof(f123,plain,
    ( spl4_10
  <=> ! [X2] :
        ( v1_finset_1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f484,plain,
    ( v1_finset_1(sK2(sK0))
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f483,f106])).

fof(f483,plain,
    ( v1_finset_1(sK2(sK0))
    | ~ v1_finset_1(sK0)
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f482,f109])).

fof(f482,plain,
    ( v1_finset_1(sK2(sK0))
    | v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f124,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f124,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | v1_finset_1(X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f479,plain,
    ( ~ spl4_6
    | spl4_9
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f475,f120])).

fof(f120,plain,
    ( ~ v1_finset_1(sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_9
  <=> ~ v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f475,plain,
    ( v1_finset_1(sK1)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f474,f131])).

fof(f131,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_12
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | v1_finset_1(X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f471,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t92_zfmisc_1)).

fof(f471,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_tarski(sK0))
        | v1_finset_1(X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f414,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f73,f60])).

fof(f60,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',redefinition_k9_setfam_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t3_subset)).

fof(f414,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(k3_tarski(sK0)))
        | v1_finset_1(X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f112,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X0)
      | v1_finset_1(X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f65,f60])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',cc2_finset_1)).

fof(f112,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_6
  <=> v1_finset_1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f465,plain,
    ( spl4_68
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f458,f105,f463])).

fof(f463,plain,
    ( spl4_68
  <=> v1_finset_1(sK3(k9_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f458,plain,
    ( v1_finset_1(sK3(k9_setfam_1(sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f418,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',existence_m1_subset_1)).

fof(f418,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | v1_finset_1(X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f106,f83])).

fof(f455,plain,
    ( ~ spl4_67
    | spl4_63 ),
    inference(avatar_split_clause,[],[f441,f437,f453])).

fof(f453,plain,
    ( spl4_67
  <=> ~ r2_hidden(sK0,k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f437,plain,
    ( spl4_63
  <=> ~ m1_subset_1(sK0,k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f441,plain,
    ( ~ r2_hidden(sK0,k9_setfam_1(k1_xboole_0))
    | ~ spl4_63 ),
    inference(resolution,[],[f438,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t1_subset)).

fof(f438,plain,
    ( ~ m1_subset_1(sK0,k9_setfam_1(k1_xboole_0))
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f437])).

fof(f448,plain,
    ( ~ spl4_65
    | spl4_63 ),
    inference(avatar_split_clause,[],[f440,f437,f446])).

fof(f446,plain,
    ( spl4_65
  <=> ~ r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f440,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_63 ),
    inference(resolution,[],[f438,f84])).

fof(f439,plain,
    ( ~ spl4_63
    | ~ spl4_0
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f420,f130,f91,f437])).

fof(f91,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f420,plain,
    ( ~ m1_subset_1(sK0,k9_setfam_1(k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_12 ),
    inference(resolution,[],[f131,f299])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k9_setfam_1(k1_xboole_0)) )
    | ~ spl4_0 ),
    inference(resolution,[],[f86,f92])).

fof(f92,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f91])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f77,f60])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t5_subset)).

fof(f431,plain,
    ( spl4_36
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f410,f289,f280])).

fof(f280,plain,
    ( spl4_36
  <=> v1_finset_1(k9_setfam_1(k3_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f289,plain,
    ( spl4_38
  <=> v1_finset_1(k3_tarski(k9_setfam_1(k3_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f410,plain,
    ( v1_finset_1(k9_setfam_1(k3_tarski(k1_xboole_0)))
    | ~ spl4_38 ),
    inference(resolution,[],[f407,f290])).

fof(f290,plain,
    ( v1_finset_1(k3_tarski(k9_setfam_1(k3_tarski(k1_xboole_0))))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f289])).

fof(f407,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k3_tarski(X0))
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f402,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(X0,k9_setfam_1(k3_tarski(X0))) ),
    inference(forward_demodulation,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t100_zfmisc_1)).

fof(f402,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k9_setfam_1(X1))
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f141,f84])).

fof(f141,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X2)))
      | v1_finset_1(X1)
      | ~ v1_finset_1(X2) ) ),
    inference(resolution,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v1_finset_1(k9_setfam_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(forward_demodulation,[],[f64,f60])).

fof(f64,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',fc17_finset_1)).

fof(f429,plain,
    ( ~ spl4_61
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f421,f130,f427])).

fof(f427,plain,
    ( spl4_61
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f421,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_12 ),
    inference(resolution,[],[f131,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',antisymmetry_r2_hidden)).

fof(f417,plain,
    ( spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f413,f111,f105])).

fof(f413,plain,
    ( v1_finset_1(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f112,f407])).

fof(f416,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f413,f103])).

fof(f103,plain,
    ( ~ v1_finset_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_5
  <=> ~ v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f412,plain,
    ( spl4_25
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | ~ spl4_25
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f408,f202])).

fof(f202,plain,
    ( ~ v1_finset_1(k1_xboole_0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl4_25
  <=> ~ v1_finset_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f408,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ spl4_28 ),
    inference(resolution,[],[f407,f227])).

fof(f227,plain,
    ( v1_finset_1(k3_tarski(k1_xboole_0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl4_28
  <=> v1_finset_1(k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f401,plain,
    ( ~ spl4_59
    | spl4_55 ),
    inference(avatar_split_clause,[],[f384,f380,f399])).

fof(f399,plain,
    ( spl4_59
  <=> ~ r2_hidden(k9_setfam_1(k1_xboole_0),k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f380,plain,
    ( spl4_55
  <=> ~ m1_subset_1(k9_setfam_1(k1_xboole_0),k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f384,plain,
    ( ~ r2_hidden(k9_setfam_1(k1_xboole_0),k9_setfam_1(k1_xboole_0))
    | ~ spl4_55 ),
    inference(resolution,[],[f381,f70])).

fof(f381,plain,
    ( ~ m1_subset_1(k9_setfam_1(k1_xboole_0),k9_setfam_1(k1_xboole_0))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f380])).

fof(f391,plain,
    ( ~ spl4_57
    | spl4_55 ),
    inference(avatar_split_clause,[],[f383,f380,f389])).

fof(f389,plain,
    ( spl4_57
  <=> ~ r1_tarski(k9_setfam_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f383,plain,
    ( ~ r1_tarski(k9_setfam_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_55 ),
    inference(resolution,[],[f381,f84])).

fof(f382,plain,
    ( ~ spl4_55
    | ~ spl4_0
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f372,f368,f91,f380])).

fof(f368,plain,
    ( spl4_52
  <=> r2_hidden(k1_xboole_0,k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f372,plain,
    ( ~ m1_subset_1(k9_setfam_1(k1_xboole_0),k9_setfam_1(k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_52 ),
    inference(resolution,[],[f369,f299])).

fof(f369,plain,
    ( r2_hidden(k1_xboole_0,k9_setfam_1(k1_xboole_0))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f368])).

fof(f375,plain,
    ( ~ spl4_49
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f374,f368,f352])).

fof(f352,plain,
    ( spl4_49
  <=> ~ v1_xboole_0(k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f374,plain,
    ( ~ v1_xboole_0(k9_setfam_1(k1_xboole_0))
    | ~ spl4_52 ),
    inference(resolution,[],[f369,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t7_boole)).

fof(f370,plain,
    ( spl4_48
    | spl4_52
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f336,f331,f368,f355])).

fof(f355,plain,
    ( spl4_48
  <=> v1_xboole_0(k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f331,plain,
    ( spl4_44
  <=> k1_xboole_0 = sK3(k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f336,plain,
    ( r2_hidden(k1_xboole_0,k9_setfam_1(k1_xboole_0))
    | v1_xboole_0(k9_setfam_1(k1_xboole_0))
    | ~ spl4_44 ),
    inference(superposition,[],[f134,f332])).

fof(f332,plain,
    ( k1_xboole_0 = sK3(k9_setfam_1(k1_xboole_0))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f331])).

fof(f134,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f72,f68])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t2_subset)).

fof(f363,plain,
    ( spl4_48
    | ~ spl4_51
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f335,f331,f361,f355])).

fof(f361,plain,
    ( spl4_51
  <=> ~ r2_hidden(k9_setfam_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f335,plain,
    ( ~ r2_hidden(k9_setfam_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k9_setfam_1(k1_xboole_0))
    | ~ spl4_44 ),
    inference(superposition,[],[f138,f332])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f134,f69])).

fof(f344,plain,
    ( spl4_46
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f337,f331,f342])).

fof(f342,plain,
    ( spl4_46
  <=> m1_subset_1(k1_xboole_0,k9_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f337,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(k1_xboole_0))
    | ~ spl4_44 ),
    inference(superposition,[],[f68,f332])).

fof(f333,plain,
    ( spl4_44
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f326,f321,f331])).

fof(f321,plain,
    ( spl4_42
  <=> v1_xboole_0(sK3(k9_setfam_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f326,plain,
    ( k1_xboole_0 = sK3(k9_setfam_1(k1_xboole_0))
    | ~ spl4_42 ),
    inference(resolution,[],[f322,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t6_boole)).

fof(f322,plain,
    ( v1_xboole_0(sK3(k9_setfam_1(k1_xboole_0)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f321])).

fof(f323,plain,
    ( spl4_42
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f314,f91,f321])).

fof(f314,plain,
    ( v1_xboole_0(sK3(k9_setfam_1(k1_xboole_0)))
    | ~ spl4_0 ),
    inference(resolution,[],[f312,f68])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f299,f134])).

fof(f306,plain,
    ( spl4_40
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f296,f289,f304])).

fof(f304,plain,
    ( spl4_40
  <=> v1_finset_1(sK3(k9_setfam_1(k3_tarski(k9_setfam_1(k3_tarski(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f296,plain,
    ( v1_finset_1(sK3(k9_setfam_1(k3_tarski(k9_setfam_1(k3_tarski(k1_xboole_0))))))
    | ~ spl4_38 ),
    inference(resolution,[],[f295,f68])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(k3_tarski(k9_setfam_1(k3_tarski(k1_xboole_0)))))
        | v1_finset_1(X0) )
    | ~ spl4_38 ),
    inference(resolution,[],[f290,f83])).

fof(f294,plain,
    ( ~ spl4_28
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl4_28
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f292,f227])).

fof(f292,plain,
    ( ~ v1_finset_1(k3_tarski(k1_xboole_0))
    | ~ spl4_37 ),
    inference(resolution,[],[f284,f82])).

fof(f284,plain,
    ( ~ v1_finset_1(k9_setfam_1(k3_tarski(k1_xboole_0)))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl4_37
  <=> ~ v1_finset_1(k9_setfam_1(k3_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f291,plain,
    ( ~ spl4_37
    | spl4_38
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f276,f226,f289,f283])).

fof(f276,plain,
    ( v1_finset_1(k3_tarski(k9_setfam_1(k3_tarski(k1_xboole_0))))
    | ~ v1_finset_1(k9_setfam_1(k3_tarski(k1_xboole_0)))
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f274,f67])).

fof(f274,plain,
    ( v1_finset_1(k3_tarski(k9_setfam_1(k3_tarski(k1_xboole_0))))
    | ~ v1_finset_1(k9_setfam_1(k3_tarski(k1_xboole_0)))
    | v1_finset_1(sK2(k9_setfam_1(k3_tarski(k1_xboole_0))))
    | ~ spl4_28 ),
    inference(resolution,[],[f66,f248])).

fof(f248,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k9_setfam_1(k3_tarski(k1_xboole_0)))
        | v1_finset_1(X1) )
    | ~ spl4_28 ),
    inference(resolution,[],[f229,f70])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(k3_tarski(k1_xboole_0)))
        | v1_finset_1(X0) )
    | ~ spl4_28 ),
    inference(resolution,[],[f227,f83])).

fof(f265,plain,
    ( spl4_34
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f256,f174,f149,f263])).

fof(f263,plain,
    ( spl4_34
  <=> v1_finset_1(sK3(k9_setfam_1(sK3(k9_setfam_1(k3_tarski(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f149,plain,
    ( spl4_14
  <=> v1_finset_1(sK3(k9_setfam_1(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f174,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f256,plain,
    ( v1_finset_1(sK3(k9_setfam_1(sK3(k9_setfam_1(k3_tarski(k1_xboole_0))))))
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f252,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f252,plain,
    ( v1_finset_1(sK3(k9_setfam_1(sK3(k9_setfam_1(k3_tarski(sK0))))))
    | ~ spl4_14 ),
    inference(resolution,[],[f152,f68])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(sK3(k9_setfam_1(k3_tarski(sK0)))))
        | v1_finset_1(X0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f150,f83])).

fof(f150,plain,
    ( v1_finset_1(sK3(k9_setfam_1(k3_tarski(sK0))))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f244,plain,
    ( spl4_32
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f198,f174,f149,f242])).

fof(f242,plain,
    ( spl4_32
  <=> v1_finset_1(sK3(k9_setfam_1(k3_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f198,plain,
    ( v1_finset_1(sK3(k9_setfam_1(k3_tarski(k1_xboole_0))))
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(superposition,[],[f150,f175])).

fof(f237,plain,
    ( ~ spl4_31
    | spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f199,f174,f162,f235])).

fof(f235,plain,
    ( spl4_31
  <=> ~ v1_finset_1(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f162,plain,
    ( spl4_19
  <=> ~ v1_finset_1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f199,plain,
    ( ~ v1_finset_1(sK3(k1_xboole_0))
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(superposition,[],[f163,f175])).

fof(f163,plain,
    ( ~ v1_finset_1(sK3(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f162])).

fof(f230,plain,
    ( ~ spl4_27
    | spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f219,f174,f127,f209])).

fof(f209,plain,
    ( spl4_27
  <=> ~ r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f127,plain,
    ( spl4_13
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f219,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f128,f175])).

fof(f128,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f228,plain,
    ( spl4_28
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f196,f174,f111,f226])).

fof(f196,plain,
    ( v1_finset_1(k3_tarski(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f112,f175])).

fof(f221,plain,
    ( ~ spl4_25
    | spl4_5
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f220,f174,f102,f201])).

fof(f220,plain,
    ( ~ v1_finset_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f103,f175])).

fof(f218,plain,
    ( ~ spl4_0
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f216,f92])).

fof(f216,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_26 ),
    inference(resolution,[],[f213,f75])).

fof(f213,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl4_26
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f214,plain,
    ( spl4_26
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f195,f174,f130,f212])).

fof(f195,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f131,f175])).

fof(f206,plain,
    ( spl4_24
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f197,f174,f105,f204])).

fof(f204,plain,
    ( spl4_24
  <=> v1_finset_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f197,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(superposition,[],[f106,f175])).

fof(f193,plain,
    ( ~ spl4_10
    | spl4_17
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f191,f157])).

fof(f157,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_17
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f191,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f190,f163])).

fof(f190,plain,
    ( v1_finset_1(sK3(sK0))
    | v1_xboole_0(sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f124,f134])).

fof(f188,plain,
    ( spl4_22
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f179,f165,f186])).

fof(f186,plain,
    ( spl4_22
  <=> v1_finset_1(sK3(k9_setfam_1(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f165,plain,
    ( spl4_18
  <=> v1_finset_1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f179,plain,
    ( v1_finset_1(sK3(k9_setfam_1(sK3(sK0))))
    | ~ spl4_18 ),
    inference(resolution,[],[f177,f68])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(sK3(sK0)))
        | v1_finset_1(X0) )
    | ~ spl4_18 ),
    inference(resolution,[],[f166,f83])).

fof(f166,plain,
    ( v1_finset_1(sK3(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f176,plain,
    ( spl4_20
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f169,f159,f174])).

fof(f159,plain,
    ( spl4_16
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f169,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_16 ),
    inference(resolution,[],[f160,f63])).

fof(f160,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f167,plain,
    ( spl4_16
    | spl4_18
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f154,f111,f165,f159])).

fof(f154,plain,
    ( v1_finset_1(sK3(sK0))
    | v1_xboole_0(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f153,f134])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | v1_finset_1(X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f143,f71])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_tarski(sK0))
        | v1_finset_1(X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f140,f84])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(k3_tarski(sK0)))
        | v1_finset_1(X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f83,f112])).

fof(f151,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f142,f111,f149])).

fof(f142,plain,
    ( v1_finset_1(sK3(k9_setfam_1(k3_tarski(sK0))))
    | ~ spl4_6 ),
    inference(resolution,[],[f140,f68])).

fof(f132,plain,
    ( ~ spl4_5
    | spl4_12
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f56,f108,f130,f102])).

fof(f56,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | r2_hidden(sK1,sK0)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK0))
      | ( ~ v1_finset_1(sK1)
        & r2_hidden(sK1,sK0) )
      | ~ v1_finset_1(sK0) )
    & ( v1_finset_1(k3_tarski(sK0))
      | ( ! [X2] :
            ( v1_finset_1(X2)
            | ~ r2_hidden(X2,sK0) )
        & v1_finset_1(sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ? [X1] :
              ( ~ v1_finset_1(X1)
              & r2_hidden(X1,X0) )
          | ~ v1_finset_1(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | ( ! [X2] :
                ( v1_finset_1(X2)
                | ~ r2_hidden(X2,X0) )
            & v1_finset_1(X0) ) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,sK0) )
        | ~ v1_finset_1(sK0) )
      & ( v1_finset_1(k3_tarski(sK0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,sK0) )
          & v1_finset_1(sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK1)
        & r2_hidden(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',t25_finset_1)).

fof(f125,plain,
    ( spl4_10
    | spl4_6 ),
    inference(avatar_split_clause,[],[f55,f111,f123])).

fof(f55,plain,(
    ! [X2] :
      ( v1_finset_1(k3_tarski(sK0))
      | v1_finset_1(X2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f121,plain,
    ( ~ spl4_5
    | ~ spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f57,f108,f119,f102])).

fof(f57,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f113,plain,
    ( spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f54,f111,f105])).

fof(f54,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f59,f98])).

fof(f98,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',d2_xboole_0)).

fof(f93,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f78,f91])).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f58,f59])).

fof(f58,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t25_finset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
