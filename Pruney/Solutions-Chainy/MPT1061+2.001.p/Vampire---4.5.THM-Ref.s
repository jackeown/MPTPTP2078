%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 395 expanded)
%              Number of leaves         :   27 (  92 expanded)
%              Depth                    :   18
%              Number of atoms          :  485 (1813 expanded)
%              Number of equality atoms :   77 ( 131 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f126,f141,f169,f177,f191,f206,f258,f322,f354])).

fof(f354,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f339,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f339,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f59,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f59,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(f322,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f305,f60])).

fof(f305,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f237,f295])).

fof(f295,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f294,f57])).

fof(f57,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f294,plain,
    ( ~ r1_tarski(sK1,sK0)
    | k1_xboole_0 = sK1
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f293,f149])).

fof(f149,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f147,f56])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_4 ),
    inference(superposition,[],[f121,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f121,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_4
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f293,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f292,f136])).

fof(f136,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f116,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f116,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f56,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f292,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_12 ),
    inference(trivial_inequality_removal,[],[f291])).

fof(f291,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_12 ),
    inference(superposition,[],[f73,f283])).

fof(f283,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f268,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f268,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f151,f235])).

fof(f235,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl5_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f151,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(subsumption_resolution,[],[f150,f56])).

fof(f150,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(superposition,[],[f58,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f58,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f237,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f221,f226])).

fof(f226,plain,
    ( ~ v1_partfun1(k2_partfun1(sK0,sK3,sK4,sK1),sK1)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f225,f105])).

fof(f105,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f225,plain,
    ( ~ v1_partfun1(k2_partfun1(sK0,sK3,sK4,sK1),sK1)
    | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f218,f108])).

fof(f108,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_3
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f218,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_partfun1(k2_partfun1(sK0,sK3,sK4,sK1),sK1)
    | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f100,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f100,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_1
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f221,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_partfun1(k2_partfun1(sK0,sK3,sK4,sK1),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f258,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_4
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_4
    | spl5_12 ),
    inference(subsumption_resolution,[],[f256,f57])).

fof(f256,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_4
    | spl5_12 ),
    inference(forward_demodulation,[],[f255,f149])).

fof(f255,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ spl5_1
    | spl5_2
    | spl5_12 ),
    inference(subsumption_resolution,[],[f254,f136])).

fof(f254,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_1
    | spl5_2
    | spl5_12 ),
    inference(trivial_inequality_removal,[],[f253])).

fof(f253,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_1
    | spl5_2
    | spl5_12 ),
    inference(superposition,[],[f252,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f252,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_1
    | spl5_2
    | spl5_12 ),
    inference(subsumption_resolution,[],[f251,f239])).

fof(f239,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f238,f54])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f238,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f224,f56])).

fof(f224,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ spl5_1 ),
    inference(superposition,[],[f100,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f251,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1
    | spl5_2
    | spl5_12 ),
    inference(superposition,[],[f250,f78])).

fof(f250,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_1
    | spl5_2
    | spl5_12 ),
    inference(subsumption_resolution,[],[f249,f154])).

fof(f154,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f153,f54])).

fof(f153,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(sK4)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f152,f56])).

fof(f152,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_2 ),
    inference(superposition,[],[f105,f88])).

fof(f249,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_1
    | spl5_12 ),
    inference(subsumption_resolution,[],[f244,f234])).

fof(f234,plain,
    ( k1_xboole_0 != sK2
    | spl5_12 ),
    inference(avatar_component_clause,[],[f233])).

fof(f244,plain,
    ( k1_xboole_0 = sK2
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f239,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f206,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f203,f136])).

fof(f203,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_10 ),
    inference(resolution,[],[f202,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f202,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f201,f54])).

fof(f201,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_funct_1(sK4)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f200,f56])).

fof(f200,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_10 ),
    inference(superposition,[],[f168,f88])).

fof(f168,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_10
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f191,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl5_9 ),
    inference(subsumption_resolution,[],[f189,f136])).

fof(f189,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f187,f151])).

fof(f187,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ v1_relat_1(sK4)
    | spl5_9 ),
    inference(superposition,[],[f185,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f185,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f184,f54])).

fof(f184,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_funct_1(sK4)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f182,f56])).

fof(f182,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_9 ),
    inference(superposition,[],[f164,f88])).

fof(f164,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl5_9
  <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f177,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl5_8 ),
    inference(subsumption_resolution,[],[f175,f136])).

fof(f175,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_8 ),
    inference(resolution,[],[f174,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f174,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f173,f54])).

fof(f173,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ v1_funct_1(sK4)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f172,f56])).

fof(f172,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_8 ),
    inference(superposition,[],[f160,f88])).

fof(f160,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_8
  <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f169,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_1 ),
    inference(avatar_split_clause,[],[f155,f99,f166,f162,f158])).

fof(f155,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_1 ),
    inference(resolution,[],[f101,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f101,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f141,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f139,plain,
    ( ~ v1_funct_1(sK4)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f137,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_3 ),
    inference(resolution,[],[f109,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f109,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f126,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f117,f123,f119])).

fof(f117,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f113,f55])).

fof(f55,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f113,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK4,sK0,sK3) ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f53,f107,f103,f99])).

fof(f53,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (7736)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.46  % (7728)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (7730)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (7734)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (7742)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (7745)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (7740)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (7726)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (7737)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (7729)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (7727)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (7732)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (7739)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (7727)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f357,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f110,f126,f141,f169,f177,f191,f206,f258,f322,f354])).
% 0.20/0.50  fof(f354,plain,(
% 0.20/0.50    ~spl5_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f353])).
% 0.20/0.50  fof(f353,plain,(
% 0.20/0.50    $false | ~spl5_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f339,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | ~spl5_5),
% 0.20/0.50    inference(backward_demodulation,[],[f59,f125])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    k1_xboole_0 = sK3 | ~spl5_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    spl5_5 <=> k1_xboole_0 = sK3),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ~v1_xboole_0(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.20/0.50    inference(ennf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f23])).
% 0.20/0.50  fof(f23,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    ~spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_12),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f321])).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    $false | (~spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f305,f60])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | (~spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_12)),
% 0.20/0.50    inference(backward_demodulation,[],[f237,f295])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | (~spl5_4 | ~spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f294,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    r1_tarski(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK0) | k1_xboole_0 = sK1 | (~spl5_4 | ~spl5_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f293,f149])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK4) | ~spl5_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f147,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_4),
% 0.20/0.50    inference(superposition,[],[f121,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl5_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl5_4 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~spl5_12),
% 0.20/0.50    inference(subsumption_resolution,[],[f292,f136])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    v1_relat_1(sK4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f116,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK3)) | v1_relat_1(sK4)),
% 0.20/0.50    inference(resolution,[],[f56,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~spl5_12),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f291])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~spl5_12),
% 0.20/0.50    inference(superposition,[],[f73,f283])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    k1_xboole_0 = k9_relat_1(sK4,sK1) | ~spl5_12),
% 0.20/0.50    inference(resolution,[],[f268,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) | ~spl5_12),
% 0.20/0.50    inference(backward_demodulation,[],[f151,f235])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | ~spl5_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f233])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    spl5_12 <=> k1_xboole_0 = sK2),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f150,f56])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.20/0.50    inference(superposition,[],[f58,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | (~spl5_1 | spl5_2 | ~spl5_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f221,f226])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ~v1_partfun1(k2_partfun1(sK0,sK3,sK4,sK1),sK1) | (~spl5_1 | spl5_2 | ~spl5_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f225,f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    ~v1_partfun1(k2_partfun1(sK0,sK3,sK4,sK1),sK1) | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | (~spl5_1 | ~spl5_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f218,f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~spl5_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f107])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    spl5_3 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_partfun1(k2_partfun1(sK0,sK3,sK4,sK1),sK1) | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~spl5_1),
% 0.20/0.50    inference(resolution,[],[f100,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl5_1 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | v1_partfun1(k2_partfun1(sK0,sK3,sK4,sK1),sK1) | ~spl5_1),
% 0.20/0.50    inference(resolution,[],[f100,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_partfun1(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    ~spl5_1 | spl5_2 | ~spl5_4 | spl5_12),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f257])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    $false | (~spl5_1 | spl5_2 | ~spl5_4 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f256,f57])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK0) | (~spl5_1 | spl5_2 | ~spl5_4 | spl5_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f255,f149])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k1_relat_1(sK4)) | (~spl5_1 | spl5_2 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f254,f136])).
% 0.20/0.50  fof(f254,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_1 | spl5_2 | spl5_12)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f253])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    sK1 != sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_1 | spl5_2 | spl5_12)),
% 0.20/0.50    inference(superposition,[],[f252,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_1 | spl5_2 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f251,f239])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f238,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    v1_funct_1(sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~spl5_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f224,f56])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | ~spl5_1),
% 0.20/0.50    inference(superposition,[],[f100,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_1 | spl5_2 | spl5_12)),
% 0.20/0.50    inference(superposition,[],[f250,f78])).
% 0.20/0.50  fof(f250,plain,(
% 0.20/0.50    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl5_1 | spl5_2 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f249,f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f153,f54])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~v1_funct_1(sK4) | spl5_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f56])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_2),
% 0.20/0.50    inference(superposition,[],[f105,f88])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_1 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f244,f234])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    k1_xboole_0 != sK2 | spl5_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f233])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~spl5_1),
% 0.20/0.50    inference(resolution,[],[f239,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    spl5_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f205])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    $false | spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f203,f136])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ~v1_relat_1(sK4) | spl5_10),
% 0.20/0.50    inference(resolution,[],[f202,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f201,f54])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_funct_1(sK4) | spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f200,f56])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_10),
% 0.20/0.50    inference(superposition,[],[f168,f88])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) | spl5_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f166])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    spl5_10 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    spl5_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f190])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    $false | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f189,f136])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    ~v1_relat_1(sK4) | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f187,f151])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~v1_relat_1(sK4) | spl5_9),
% 0.20/0.50    inference(superposition,[],[f185,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f184,f54])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_funct_1(sK4) | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f182,f56])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_9),
% 0.20/0.50    inference(superposition,[],[f164,f88])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | spl5_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f162])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    spl5_9 <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    spl5_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f176])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    $false | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f175,f136])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    ~v1_relat_1(sK4) | spl5_8),
% 0.20/0.50    inference(resolution,[],[f174,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f173,f54])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~v1_funct_1(sK4) | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f172,f56])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_8),
% 0.20/0.50    inference(superposition,[],[f160,f88])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f158])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    spl5_8 <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f155,f99,f166,f162,f158])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_1),
% 0.20/0.50    inference(resolution,[],[f101,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f99])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    spl5_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    $false | spl5_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f139,f54])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ~v1_funct_1(sK4) | spl5_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f137,f56])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_3),
% 0.20/0.50    inference(resolution,[],[f109,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f107])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl5_4 | spl5_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f117,f123,f119])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f113,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    v1_funct_2(sK4,sK0,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~v1_funct_2(sK4,sK0,sK3)),
% 0.20/0.50    inference(resolution,[],[f56,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f53,f107,f103,f99])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (7727)------------------------------
% 0.20/0.50  % (7727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7727)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (7727)Memory used [KB]: 10746
% 0.20/0.50  % (7727)Time elapsed: 0.089 s
% 0.20/0.50  % (7727)------------------------------
% 0.20/0.50  % (7727)------------------------------
% 0.20/0.50  % (7744)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (7743)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (7738)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (7731)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.20/0.51  % (7722)Success in time 0.155 s
%------------------------------------------------------------------------------
