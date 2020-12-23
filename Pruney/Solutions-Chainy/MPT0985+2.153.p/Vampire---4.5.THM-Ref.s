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
% DateTime   : Thu Dec  3 13:02:23 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  291 (1034 expanded)
%              Number of leaves         :   40 ( 299 expanded)
%              Depth                    :   22
%              Number of atoms          : 1049 (4822 expanded)
%              Number of equality atoms :  121 ( 677 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2527,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f126,f506,f590,f598,f778,f1281,f1410,f1502,f1696,f1726,f1747,f1878,f2023,f2305,f2309,f2438,f2486,f2487,f2525])).

fof(f2525,plain,
    ( spl9_2
    | ~ spl9_18
    | ~ spl9_69 ),
    inference(avatar_contradiction_clause,[],[f2524])).

fof(f2524,plain,
    ( $false
    | spl9_2
    | ~ spl9_18
    | ~ spl9_69 ),
    inference(subsumption_resolution,[],[f886,f1280])).

fof(f1280,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl9_69 ),
    inference(avatar_component_clause,[],[f1279])).

fof(f1279,plain,
    ( spl9_69
  <=> ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f886,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK6)
    | spl9_2
    | ~ spl9_18 ),
    inference(backward_demodulation,[],[f677,f380])).

fof(f380,plain,
    ( k1_xboole_0 = sK8
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl9_18
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f677,plain,
    ( ~ v4_relat_1(sK8,sK6)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f674,f127])).

fof(f127,plain,(
    v1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f123,f80])).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f123,plain,
    ( v1_relat_1(sK8)
    | ~ v1_relat_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(resolution,[],[f67,f60])).

fof(f60,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
      | ~ v1_funct_2(k2_funct_1(sK8),sK7,sK6)
      | ~ v1_funct_1(k2_funct_1(sK8)) )
    & sK7 = k2_relset_1(sK6,sK7,sK8)
    & v2_funct_1(sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK8,sK6,sK7)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f18,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
        | ~ v1_funct_2(k2_funct_1(sK8),sK7,sK6)
        | ~ v1_funct_1(k2_funct_1(sK8)) )
      & sK7 = k2_relset_1(sK6,sK7,sK8)
      & v2_funct_1(sK8)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK8,sK6,sK7)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

% (27260)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f674,plain,
    ( ~ v4_relat_1(sK8,sK6)
    | ~ v1_relat_1(sK8)
    | spl9_2 ),
    inference(resolution,[],[f645,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f645,plain,
    ( ~ r1_tarski(k1_relat_1(sK8),sK6)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f644,f127])).

fof(f644,plain,
    ( ~ r1_tarski(k1_relat_1(sK8),sK6)
    | ~ v1_relat_1(sK8)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f643,f58])).

fof(f58,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f643,plain,
    ( ~ r1_tarski(k1_relat_1(sK8),sK6)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f642,f61])).

fof(f61,plain,(
    v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f642,plain,
    ( ~ r1_tarski(k1_relat_1(sK8),sK6)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_2 ),
    inference(resolution,[],[f641,f244])).

fof(f244,plain,(
    ! [X2,X3] :
      ( sP2(X3,k2_funct_1(X2))
      | ~ r1_tarski(k1_relat_1(X2),X3)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f243,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f243,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),X3)
      | sP2(X3,k2_funct_1(X2))
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f237,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f237,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),X3)
      | sP2(X3,k2_funct_1(X2))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f86,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP2(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f641,plain,
    ( ~ sP2(sK6,k2_funct_1(sK8))
    | spl9_2 ),
    inference(resolution,[],[f609,f113])).

fof(f113,plain,
    ( ~ v1_funct_2(k2_funct_1(sK8),sK7,sK6)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl9_2
  <=> v1_funct_2(k2_funct_1(sK8),sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f609,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK8),sK7,X3)
      | ~ sP2(X3,k2_funct_1(sK8)) ) ),
    inference(subsumption_resolution,[],[f608,f127])).

fof(f608,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK8),sK7,X3)
      | ~ sP2(X3,k2_funct_1(sK8))
      | ~ v1_relat_1(sK8) ) ),
    inference(subsumption_resolution,[],[f607,f58])).

fof(f607,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK8),sK7,X3)
      | ~ sP2(X3,k2_funct_1(sK8))
      | ~ v1_funct_1(sK8)
      | ~ v1_relat_1(sK8) ) ),
    inference(subsumption_resolution,[],[f604,f61])).

fof(f604,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK8),sK7,X3)
      | ~ sP2(X3,k2_funct_1(sK8))
      | ~ v2_funct_1(sK8)
      | ~ v1_funct_1(sK8)
      | ~ v1_relat_1(sK8) ) ),
    inference(superposition,[],[f222,f265])).

fof(f265,plain,(
    sK7 = k2_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f263,f60])).

fof(f263,plain,
    ( sK7 = k2_relat_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(superposition,[],[f90,f62])).

fof(f62,plain,(
    sK7 = k2_relset_1(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f222,plain,(
    ! [X6,X7] :
      ( v1_funct_2(k2_funct_1(X6),k2_relat_1(X6),X7)
      | ~ sP2(X7,k2_funct_1(X6))
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f84,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f2487,plain,
    ( spl9_18
    | ~ spl9_45
    | spl9_70 ),
    inference(avatar_split_clause,[],[f1785,f1285,f900,f378])).

fof(f900,plain,
    ( spl9_45
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f1285,plain,
    ( spl9_70
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f1785,plain,
    ( k1_xboole_0 = sK8
    | ~ spl9_45
    | spl9_70 ),
    inference(subsumption_resolution,[],[f1784,f1286])).

fof(f1286,plain,
    ( k1_xboole_0 != sK6
    | spl9_70 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1784,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK8
    | ~ spl9_45 ),
    inference(subsumption_resolution,[],[f1783,f1761])).

fof(f1761,plain,
    ( v1_funct_2(sK8,sK6,k1_xboole_0)
    | ~ spl9_45 ),
    inference(backward_demodulation,[],[f59,f902])).

fof(f902,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f900])).

fof(f59,plain,(
    v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f1783,plain,
    ( ~ v1_funct_2(sK8,sK6,k1_xboole_0)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK8
    | ~ spl9_45 ),
    inference(resolution,[],[f1767,f104])).

fof(f104,plain,(
    ! [X2,X0] :
      ( ~ sP5(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP5(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP5(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f1767,plain,
    ( sP5(sK8,k1_xboole_0,sK6)
    | ~ spl9_45 ),
    inference(backward_demodulation,[],[f193,f902])).

fof(f193,plain,(
    sP5(sK8,sK7,sK6) ),
    inference(resolution,[],[f99,f60])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP5(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X2,X1,X0)
        & sP4(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f34,f43,f42,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f2486,plain,
    ( ~ spl9_36
    | ~ spl9_70 ),
    inference(avatar_contradiction_clause,[],[f2485])).

fof(f2485,plain,
    ( $false
    | ~ spl9_36
    | ~ spl9_70 ),
    inference(subsumption_resolution,[],[f2484,f105])).

% (27266)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f105,plain,(
    ! [X1] : ~ sP3(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f2484,plain,
    ( sP3(k1_xboole_0,k1_xboole_0)
    | ~ spl9_36
    | ~ spl9_70 ),
    inference(backward_demodulation,[],[f799,f1287])).

fof(f1287,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_70 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f799,plain,
    ( sP3(sK6,k1_xboole_0)
    | ~ spl9_36 ),
    inference(backward_demodulation,[],[f720,f779])).

fof(f779,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_36 ),
    inference(resolution,[],[f720,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f720,plain,
    ( sP3(sK6,sK7)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f718])).

fof(f718,plain,
    ( spl9_36
  <=> sP3(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f2438,plain,
    ( ~ spl9_1
    | spl9_3
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_45
    | ~ spl9_72
    | ~ spl9_82 ),
    inference(avatar_contradiction_clause,[],[f2432])).

fof(f2432,plain,
    ( $false
    | ~ spl9_1
    | spl9_3
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_45
    | ~ spl9_72
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f1894,f2431])).

fof(f2431,plain,
    ( ! [X0] : m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_72
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f1630,f2342])).

fof(f2342,plain,
    ( ! [X0] : sP2(X0,k2_funct_1(k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f2341,f878])).

fof(f878,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f470,f380])).

fof(f470,plain,
    ( v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl9_20
  <=> v1_relat_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f2341,plain,
    ( ! [X0] :
        ( sP2(X0,k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f2336,f874])).

fof(f874,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_18 ),
    inference(backward_demodulation,[],[f108,f380])).

fof(f108,plain,
    ( v1_funct_1(k2_funct_1(sK8))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl9_1
  <=> v1_funct_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2336,plain,
    ( ! [X0] :
        ( sP2(X0,k2_funct_1(k1_xboole_0))
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_82 ),
    inference(resolution,[],[f2315,f86])).

fof(f2315,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0)
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f2314,f878])).

fof(f2314,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0)
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_31
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f2313,f874])).

fof(f2313,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0)
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl9_18
    | ~ spl9_31
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f2312,f881])).

fof(f881,plain,
    ( v2_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_18
    | ~ spl9_31 ),
    inference(backward_demodulation,[],[f571,f380])).

fof(f571,plain,
    ( v2_funct_1(k2_funct_1(sK8))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f570])).

fof(f570,plain,
    ( spl9_31
  <=> v2_funct_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f2312,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0)
        | ~ v2_funct_1(k2_funct_1(k1_xboole_0))
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl9_82 ),
    inference(resolution,[],[f2022,f231])).

fof(f231,plain,(
    ! [X2,X3] :
      ( ~ v4_relat_1(k2_funct_1(X2),X3)
      | r1_tarski(k2_relat_1(X2),X3)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f220,f76])).

% (27262)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f220,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_relat_1(X2),X3)
      | ~ v4_relat_1(k2_funct_1(X2),X3)
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f81,f78])).

fof(f2022,plain,
    ( ! [X0] : v4_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0)),X0)
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f2021])).

fof(f2021,plain,
    ( spl9_82
  <=> ! [X0] : v4_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f1630,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ sP2(X0,k2_funct_1(k1_xboole_0)) )
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f1629,plain,
    ( spl9_72
  <=> ! [X0] :
        ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ sP2(X0,k2_funct_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f1894,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6)))
    | spl9_3
    | ~ spl9_18
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f1765,f380])).

fof(f1765,plain,
    ( ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6)))
    | spl9_3
    | ~ spl9_45 ),
    inference(backward_demodulation,[],[f117,f902])).

fof(f117,plain,
    ( ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl9_3
  <=> m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f2309,plain,
    ( spl9_72
    | ~ spl9_18
    | ~ spl9_21
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f2279,f900,f473,f378,f1629])).

fof(f473,plain,
    ( spl9_21
  <=> sK7 = k1_relat_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f2279,plain,
    ( ! [X3] :
        ( ~ sP2(X3,k2_funct_1(k1_xboole_0))
        | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) )
    | ~ spl9_18
    | ~ spl9_21
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f2278,f380])).

fof(f2278,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
        | ~ sP2(X3,k2_funct_1(sK8)) )
    | ~ spl9_18
    | ~ spl9_21
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f2277,f380])).

fof(f2277,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
        | ~ sP2(X3,k2_funct_1(sK8)) )
    | ~ spl9_21
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f526,f902])).

fof(f526,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,X3)))
        | ~ sP2(X3,k2_funct_1(sK8)) )
    | ~ spl9_21 ),
    inference(superposition,[],[f85,f475])).

fof(f475,plain,
    ( sK7 = k1_relat_1(k2_funct_1(sK8))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f473])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2305,plain,
    ( ~ spl9_1
    | spl9_3
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_31
    | ~ spl9_45
    | ~ spl9_80 ),
    inference(avatar_contradiction_clause,[],[f2299])).

fof(f2299,plain,
    ( $false
    | ~ spl9_1
    | spl9_3
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_31
    | ~ spl9_45
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f1894,f2280])).

fof(f2280,plain,
    ( ! [X3] : m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_31
    | ~ spl9_45
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f2279,f2232])).

fof(f2232,plain,
    ( ! [X0] : sP2(X0,k2_funct_1(k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f2231,f878])).

fof(f2231,plain,
    ( ! [X0] :
        ( sP2(X0,k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f2230,f874])).

fof(f2230,plain,
    ( ! [X0] :
        ( sP2(X0,k2_funct_1(k1_xboole_0))
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f2200,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2200,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | sP2(X0,k2_funct_1(k1_xboole_0))
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_80 ),
    inference(superposition,[],[f86,f2059])).

fof(f2059,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_80 ),
    inference(forward_demodulation,[],[f2058,f64])).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f2058,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f2057,f878])).

fof(f2057,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_31
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f2056,f874])).

fof(f2056,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_18
    | ~ spl9_31
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f2040,f881])).

% (27276)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f2040,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v2_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_80 ),
    inference(superposition,[],[f78,f2013])).

fof(f2013,plain,
    ( k1_xboole_0 = k2_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f2011,plain,
    ( spl9_80
  <=> k1_xboole_0 = k2_funct_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f2023,plain,
    ( spl9_82
    | spl9_80
    | ~ spl9_18
    | ~ spl9_32
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1999,f718,f574,f378,f2011,f2021])).

fof(f574,plain,
    ( spl9_32
  <=> sP2(sK7,k2_funct_1(k2_funct_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f1999,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_funct_1(k2_funct_1(k1_xboole_0))
        | v4_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0)),X0) )
    | ~ spl9_18
    | ~ spl9_32
    | ~ spl9_36 ),
    inference(resolution,[],[f1892,f369])).

fof(f369,plain,(
    ! [X4,X5] :
      ( ~ sP2(k1_xboole_0,X4)
      | k1_xboole_0 = X4
      | v4_relat_1(X4,X5) ) ),
    inference(subsumption_resolution,[],[f368,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f180,f80])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | v1_relat_1(X1)
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(resolution,[],[f85,f67])).

fof(f368,plain,(
    ! [X4,X5] :
      ( v4_relat_1(X4,X5)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = X4
      | ~ sP2(k1_xboole_0,X4) ) ),
    inference(subsumption_resolution,[],[f354,f66])).

fof(f354,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_xboole_0,X5)
      | v4_relat_1(X4,X5)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = X4
      | ~ sP2(k1_xboole_0,X4) ) ),
    inference(superposition,[],[f82,f349])).

fof(f349,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ sP2(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f346,f84])).

fof(f346,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,k1_relat_1(X0),k1_xboole_0)
      | k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ sP2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f104,f195])).

fof(f195,plain,(
    ! [X2,X1] :
      ( sP5(X1,X2,k1_relat_1(X1))
      | ~ sP2(X2,X1) ) ),
    inference(resolution,[],[f99,f85])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1892,plain,
    ( sP2(k1_xboole_0,k2_funct_1(k2_funct_1(k1_xboole_0)))
    | ~ spl9_18
    | ~ spl9_32
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f797,f380])).

fof(f797,plain,
    ( sP2(k1_xboole_0,k2_funct_1(k2_funct_1(sK8)))
    | ~ spl9_32
    | ~ spl9_36 ),
    inference(backward_demodulation,[],[f576,f779])).

fof(f576,plain,
    ( sP2(sK7,k2_funct_1(k2_funct_1(sK8)))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f574])).

fof(f1878,plain,
    ( spl9_6
    | ~ spl9_18
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f1877,f900,f378,f144])).

fof(f144,plain,
    ( spl9_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1877,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl9_18
    | ~ spl9_45 ),
    inference(subsumption_resolution,[],[f1876,f80])).

fof(f1876,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k2_zfmisc_1(sK6,k1_xboole_0))
    | ~ spl9_18
    | ~ spl9_45 ),
    inference(resolution,[],[f1849,f67])).

fof(f1849,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)))
    | ~ spl9_18
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f1762,f380])).

fof(f1762,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)))
    | ~ spl9_45 ),
    inference(backward_demodulation,[],[f60,f902])).

fof(f1747,plain,
    ( spl9_45
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1746,f718,f900])).

fof(f1746,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_36 ),
    inference(resolution,[],[f720,f96])).

fof(f1726,plain,
    ( spl9_35
    | spl9_36 ),
    inference(avatar_split_clause,[],[f1000,f718,f714])).

fof(f714,plain,
    ( spl9_35
  <=> sK6 = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f1000,plain,
    ( sP3(sK6,sK7)
    | sK6 = k1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f996,f59])).

fof(f996,plain,
    ( ~ v1_funct_2(sK8,sK6,sK7)
    | sP3(sK6,sK7)
    | sK6 = k1_relat_1(sK8) ),
    inference(resolution,[],[f60,f396])).

fof(f396,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP3(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f394,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f394,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP3(X3,X4)
      | ~ sP4(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f94,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f1696,plain,
    ( spl9_3
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_35 ),
    inference(avatar_contradiction_clause,[],[f1695])).

fof(f1695,plain,
    ( $false
    | spl9_3
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f1694,f117])).

fof(f1694,plain,
    ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_35 ),
    inference(forward_demodulation,[],[f1693,f475])).

fof(f1693,plain,
    ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6)))
    | ~ spl9_26
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f1692,f127])).

fof(f1692,plain,
    ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6)))
    | ~ v1_relat_1(sK8)
    | ~ spl9_26
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f1691,f58])).

fof(f1691,plain,
    ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6)))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_26
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f1690,f61])).

fof(f1690,plain,
    ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6)))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_26
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f1670,f542])).

fof(f542,plain,
    ( sP1(k2_funct_1(sK8))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl9_26
  <=> sP1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f1670,plain,
    ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6)))
    | ~ sP1(k2_funct_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_35 ),
    inference(superposition,[],[f236,f716])).

fof(f716,plain,
    ( sK6 = k1_relat_1(sK8)
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f714])).

fof(f236,plain,(
    ! [X1] :
      ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
      | ~ sP1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f74,f79])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1502,plain,
    ( spl9_32
    | ~ spl9_1
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f1501,f570,f473,f469,f107,f574])).

fof(f1501,plain,
    ( sP2(sK7,k2_funct_1(k2_funct_1(sK8)))
    | ~ spl9_1
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1500,f470])).

fof(f1500,plain,
    ( sP2(sK7,k2_funct_1(k2_funct_1(sK8)))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_1
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1499,f108])).

fof(f1499,plain,
    ( sP2(sK7,k2_funct_1(k2_funct_1(sK8)))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1472,f571])).

fof(f1472,plain,
    ( sP2(sK7,k2_funct_1(k2_funct_1(sK8)))
    | ~ v2_funct_1(k2_funct_1(sK8))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_21 ),
    inference(superposition,[],[f246,f475])).

fof(f246,plain,(
    ! [X8] :
      ( sP2(k1_relat_1(X8),k2_funct_1(X8))
      | ~ v2_funct_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f245,f76])).

fof(f245,plain,(
    ! [X8] :
      ( sP2(k1_relat_1(X8),k2_funct_1(X8))
      | ~ v1_relat_1(k2_funct_1(X8))
      | ~ v2_funct_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f242,f77])).

fof(f242,plain,(
    ! [X8] :
      ( sP2(k1_relat_1(X8),k2_funct_1(X8))
      | ~ v1_funct_1(k2_funct_1(X8))
      | ~ v1_relat_1(k2_funct_1(X8))
      | ~ v2_funct_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f208,f79])).

fof(f208,plain,(
    ! [X0] :
      ( sP2(k2_relat_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f86,f100])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1410,plain,
    ( spl9_21
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f1409,f469,f473])).

fof(f1409,plain,
    ( sK7 = k1_relat_1(k2_funct_1(sK8))
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f1408,f470])).

fof(f1408,plain,
    ( sK7 = k1_relat_1(k2_funct_1(sK8))
    | ~ v1_relat_1(k2_funct_1(sK8)) ),
    inference(subsumption_resolution,[],[f1403,f321])).

fof(f321,plain,(
    v4_relat_1(k2_funct_1(sK8),sK7) ),
    inference(subsumption_resolution,[],[f320,f127])).

fof(f320,plain,
    ( v4_relat_1(k2_funct_1(sK8),sK7)
    | ~ v1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f319,f58])).

fof(f319,plain,
    ( v4_relat_1(k2_funct_1(sK8),sK7)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f275,f61])).

fof(f275,plain,
    ( v4_relat_1(k2_funct_1(sK8),sK7)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8) ),
    inference(superposition,[],[f233,f265])).

fof(f233,plain,(
    ! [X10] :
      ( v4_relat_1(k2_funct_1(X10),k2_relat_1(X10))
      | ~ v2_funct_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X10) ) ),
    inference(subsumption_resolution,[],[f224,f76])).

fof(f224,plain,(
    ! [X10] :
      ( v4_relat_1(k2_funct_1(X10),k2_relat_1(X10))
      | ~ v1_relat_1(k2_funct_1(X10))
      | ~ v2_funct_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X10) ) ),
    inference(superposition,[],[f154,f78])).

fof(f154,plain,(
    ! [X0] :
      ( v4_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f82,f100])).

fof(f1403,plain,
    ( sK7 = k1_relat_1(k2_funct_1(sK8))
    | ~ v4_relat_1(k2_funct_1(sK8),sK7)
    | ~ v1_relat_1(k2_funct_1(sK8)) ),
    inference(resolution,[],[f990,f160])).

fof(f160,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(X3))
      | k1_relat_1(X3) = X2
      | ~ v4_relat_1(X3,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f89,f81])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f990,plain,(
    r1_tarski(sK7,k1_relat_1(k2_funct_1(sK8))) ),
    inference(subsumption_resolution,[],[f989,f127])).

fof(f989,plain,
    ( r1_tarski(sK7,k1_relat_1(k2_funct_1(sK8)))
    | ~ v1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f988,f58])).

fof(f988,plain,
    ( r1_tarski(sK7,k1_relat_1(k2_funct_1(sK8)))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f955,f61])).

fof(f955,plain,
    ( r1_tarski(sK7,k1_relat_1(k2_funct_1(sK8)))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8) ),
    inference(superposition,[],[f442,f265])).

fof(f442,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X1)))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f435,f76])).

fof(f435,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X1)))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X1)) ) ),
    inference(resolution,[],[f231,f154])).

fof(f1281,plain,
    ( ~ spl9_6
    | spl9_69 ),
    inference(avatar_split_clause,[],[f1277,f1279,f144])).

fof(f1277,plain,(
    ! [X0] :
      ( v4_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f156,f66])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v4_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f82,f64])).

fof(f778,plain,
    ( spl9_2
    | ~ spl9_35 ),
    inference(avatar_contradiction_clause,[],[f777])).

fof(f777,plain,
    ( $false
    | spl9_2
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f776,f127])).

fof(f776,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_2
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f775,f58])).

fof(f775,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_2
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f774,f61])).

fof(f774,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_2
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f747,f641])).

fof(f747,plain,
    ( sP2(sK6,k2_funct_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_35 ),
    inference(superposition,[],[f246,f716])).

fof(f598,plain,(
    spl9_31 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | spl9_31 ),
    inference(subsumption_resolution,[],[f596,f127])).

fof(f596,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_31 ),
    inference(subsumption_resolution,[],[f595,f58])).

fof(f595,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_31 ),
    inference(subsumption_resolution,[],[f594,f61])).

fof(f594,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_31 ),
    inference(resolution,[],[f593,f71])).

fof(f71,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f21,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f593,plain,
    ( ~ sP0(sK8)
    | spl9_31 ),
    inference(resolution,[],[f572,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f572,plain,
    ( ~ v2_funct_1(k2_funct_1(sK8))
    | spl9_31 ),
    inference(avatar_component_clause,[],[f570])).

fof(f590,plain,
    ( ~ spl9_1
    | ~ spl9_20
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_20
    | spl9_26 ),
    inference(subsumption_resolution,[],[f588,f470])).

fof(f588,plain,
    ( ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_1
    | spl9_26 ),
    inference(subsumption_resolution,[],[f587,f108])).

fof(f587,plain,
    ( ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | spl9_26 ),
    inference(resolution,[],[f543,f75])).

fof(f75,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f23,f37])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f543,plain,
    ( ~ sP1(k2_funct_1(sK8))
    | spl9_26 ),
    inference(avatar_component_clause,[],[f541])).

fof(f506,plain,(
    spl9_20 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | spl9_20 ),
    inference(subsumption_resolution,[],[f504,f127])).

fof(f504,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_20 ),
    inference(subsumption_resolution,[],[f502,f58])).

fof(f502,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_20 ),
    inference(resolution,[],[f471,f76])).

fof(f471,plain,
    ( ~ v1_relat_1(k2_funct_1(sK8))
    | spl9_20 ),
    inference(avatar_component_clause,[],[f469])).

fof(f126,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f124,f80])).

fof(f124,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK6,sK7))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f123,f122])).

fof(f122,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f121,f58])).

fof(f121,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_1 ),
    inference(resolution,[],[f77,f109])).

fof(f109,plain,
    ( ~ v1_funct_1(k2_funct_1(sK8))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f118,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f63,f115,f111,f107])).

fof(f63,plain,
    ( ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
    | ~ v1_funct_2(k2_funct_1(sK8),sK7,sK6)
    | ~ v1_funct_1(k2_funct_1(sK8)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (27267)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (27273)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (27264)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (27256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (27257)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.27/0.53  % (27265)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.27/0.53  % (27271)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.27/0.53  % (27270)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.27/0.53  % (27253)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.53  % (27275)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.39/0.53  % (27268)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.39/0.53  % (27272)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.39/0.53  % (27254)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.39/0.53  % (27252)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.39/0.54  % (27256)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % (27274)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.39/0.54  % (27255)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.39/0.54  % (27259)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.39/0.54  % (27261)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f2527,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(avatar_sat_refutation,[],[f118,f126,f506,f590,f598,f778,f1281,f1410,f1502,f1696,f1726,f1747,f1878,f2023,f2305,f2309,f2438,f2486,f2487,f2525])).
% 1.39/0.54  fof(f2525,plain,(
% 1.39/0.54    spl9_2 | ~spl9_18 | ~spl9_69),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f2524])).
% 1.39/0.54  fof(f2524,plain,(
% 1.39/0.54    $false | (spl9_2 | ~spl9_18 | ~spl9_69)),
% 1.39/0.54    inference(subsumption_resolution,[],[f886,f1280])).
% 1.39/0.54  fof(f1280,plain,(
% 1.39/0.54    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | ~spl9_69),
% 1.39/0.54    inference(avatar_component_clause,[],[f1279])).
% 1.39/0.54  fof(f1279,plain,(
% 1.39/0.54    spl9_69 <=> ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).
% 1.39/0.54  fof(f886,plain,(
% 1.39/0.54    ~v4_relat_1(k1_xboole_0,sK6) | (spl9_2 | ~spl9_18)),
% 1.39/0.54    inference(backward_demodulation,[],[f677,f380])).
% 1.39/0.54  fof(f380,plain,(
% 1.39/0.54    k1_xboole_0 = sK8 | ~spl9_18),
% 1.39/0.54    inference(avatar_component_clause,[],[f378])).
% 1.39/0.54  fof(f378,plain,(
% 1.39/0.54    spl9_18 <=> k1_xboole_0 = sK8),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.39/0.54  fof(f677,plain,(
% 1.39/0.54    ~v4_relat_1(sK8,sK6) | spl9_2),
% 1.39/0.54    inference(subsumption_resolution,[],[f674,f127])).
% 1.39/0.54  fof(f127,plain,(
% 1.39/0.54    v1_relat_1(sK8)),
% 1.39/0.54    inference(subsumption_resolution,[],[f123,f80])).
% 1.39/0.54  fof(f80,plain,(
% 1.39/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.39/0.54  fof(f123,plain,(
% 1.39/0.54    v1_relat_1(sK8) | ~v1_relat_1(k2_zfmisc_1(sK6,sK7))),
% 1.39/0.54    inference(resolution,[],[f67,f60])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 1.39/0.54    inference(cnf_transformation,[],[f46])).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    (~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) | ~v1_funct_2(k2_funct_1(sK8),sK7,sK6) | ~v1_funct_1(k2_funct_1(sK8))) & sK7 = k2_relset_1(sK6,sK7,sK8) & v2_funct_1(sK8) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8)),
% 1.39/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f18,f45])).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) | ~v1_funct_2(k2_funct_1(sK8),sK7,sK6) | ~v1_funct_1(k2_funct_1(sK8))) & sK7 = k2_relset_1(sK6,sK7,sK8) & v2_funct_1(sK8) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8))),
% 1.39/0.54    introduced(choice_axiom,[])).
% 1.39/0.54  % (27260)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.39/0.54    inference(flattening,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.39/0.54    inference(ennf_transformation,[],[f16])).
% 1.39/0.54  fof(f16,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.39/0.54    inference(negated_conjecture,[],[f15])).
% 1.39/0.54  fof(f15,conjecture,(
% 1.39/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.39/0.54  fof(f67,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.39/0.54  fof(f674,plain,(
% 1.39/0.54    ~v4_relat_1(sK8,sK6) | ~v1_relat_1(sK8) | spl9_2),
% 1.39/0.54    inference(resolution,[],[f645,f81])).
% 1.39/0.54  fof(f81,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f49])).
% 1.39/0.54  fof(f49,plain,(
% 1.39/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(nnf_transformation,[],[f28])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.39/0.54  fof(f645,plain,(
% 1.39/0.54    ~r1_tarski(k1_relat_1(sK8),sK6) | spl9_2),
% 1.39/0.54    inference(subsumption_resolution,[],[f644,f127])).
% 1.39/0.54  fof(f644,plain,(
% 1.39/0.54    ~r1_tarski(k1_relat_1(sK8),sK6) | ~v1_relat_1(sK8) | spl9_2),
% 1.39/0.54    inference(subsumption_resolution,[],[f643,f58])).
% 1.39/0.54  fof(f58,plain,(
% 1.39/0.54    v1_funct_1(sK8)),
% 1.39/0.54    inference(cnf_transformation,[],[f46])).
% 1.39/0.54  fof(f643,plain,(
% 1.39/0.54    ~r1_tarski(k1_relat_1(sK8),sK6) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_2),
% 1.39/0.54    inference(subsumption_resolution,[],[f642,f61])).
% 1.39/0.54  fof(f61,plain,(
% 1.39/0.54    v2_funct_1(sK8)),
% 1.39/0.54    inference(cnf_transformation,[],[f46])).
% 1.39/0.54  fof(f642,plain,(
% 1.39/0.54    ~r1_tarski(k1_relat_1(sK8),sK6) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_2),
% 1.39/0.54    inference(resolution,[],[f641,f244])).
% 1.39/0.54  fof(f244,plain,(
% 1.39/0.54    ( ! [X2,X3] : (sP2(X3,k2_funct_1(X2)) | ~r1_tarski(k1_relat_1(X2),X3) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f243,f76])).
% 1.39/0.54  fof(f76,plain,(
% 1.39/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f25])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(flattening,[],[f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.39/0.54  fof(f243,plain,(
% 1.39/0.54    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),X3) | sP2(X3,k2_funct_1(X2)) | ~v1_relat_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f237,f77])).
% 1.39/0.54  fof(f77,plain,(
% 1.39/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f25])).
% 1.39/0.54  fof(f237,plain,(
% 1.39/0.54    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),X3) | sP2(X3,k2_funct_1(X2)) | ~v1_funct_1(k2_funct_1(X2)) | ~v1_relat_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.39/0.54    inference(superposition,[],[f86,f79])).
% 1.39/0.54  fof(f79,plain,(
% 1.39/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f27])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(flattening,[],[f26])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.39/0.54  fof(f86,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP2(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f40])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ! [X0,X1] : (sP2(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(definition_folding,[],[f30,f39])).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP2(X0,X1))),
% 1.39/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(flattening,[],[f29])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.39/0.54    inference(ennf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,axiom,(
% 1.39/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.39/0.54  fof(f641,plain,(
% 1.39/0.54    ~sP2(sK6,k2_funct_1(sK8)) | spl9_2),
% 1.39/0.54    inference(resolution,[],[f609,f113])).
% 1.39/0.54  fof(f113,plain,(
% 1.39/0.54    ~v1_funct_2(k2_funct_1(sK8),sK7,sK6) | spl9_2),
% 1.39/0.54    inference(avatar_component_clause,[],[f111])).
% 1.39/0.54  fof(f111,plain,(
% 1.39/0.54    spl9_2 <=> v1_funct_2(k2_funct_1(sK8),sK7,sK6)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.39/0.54  fof(f609,plain,(
% 1.39/0.54    ( ! [X3] : (v1_funct_2(k2_funct_1(sK8),sK7,X3) | ~sP2(X3,k2_funct_1(sK8))) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f608,f127])).
% 1.39/0.54  fof(f608,plain,(
% 1.39/0.54    ( ! [X3] : (v1_funct_2(k2_funct_1(sK8),sK7,X3) | ~sP2(X3,k2_funct_1(sK8)) | ~v1_relat_1(sK8)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f607,f58])).
% 1.39/0.54  fof(f607,plain,(
% 1.39/0.54    ( ! [X3] : (v1_funct_2(k2_funct_1(sK8),sK7,X3) | ~sP2(X3,k2_funct_1(sK8)) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f604,f61])).
% 1.39/0.54  fof(f604,plain,(
% 1.39/0.54    ( ! [X3] : (v1_funct_2(k2_funct_1(sK8),sK7,X3) | ~sP2(X3,k2_funct_1(sK8)) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8)) )),
% 1.39/0.54    inference(superposition,[],[f222,f265])).
% 1.39/0.54  fof(f265,plain,(
% 1.39/0.54    sK7 = k2_relat_1(sK8)),
% 1.39/0.54    inference(subsumption_resolution,[],[f263,f60])).
% 1.39/0.54  fof(f263,plain,(
% 1.39/0.54    sK7 = k2_relat_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 1.39/0.54    inference(superposition,[],[f90,f62])).
% 1.39/0.54  fof(f62,plain,(
% 1.39/0.54    sK7 = k2_relset_1(sK6,sK7,sK8)),
% 1.39/0.54    inference(cnf_transformation,[],[f46])).
% 1.39/0.54  fof(f90,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.39/0.54  fof(f222,plain,(
% 1.39/0.54    ( ! [X6,X7] : (v1_funct_2(k2_funct_1(X6),k2_relat_1(X6),X7) | ~sP2(X7,k2_funct_1(X6)) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 1.39/0.54    inference(superposition,[],[f84,f78])).
% 1.39/0.54  fof(f78,plain,(
% 1.39/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f27])).
% 1.39/0.54  fof(f84,plain,(
% 1.39/0.54    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP2(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f50])).
% 1.39/0.54  fof(f50,plain,(
% 1.39/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP2(X0,X1))),
% 1.39/0.54    inference(nnf_transformation,[],[f39])).
% 1.39/0.55  fof(f2487,plain,(
% 1.39/0.55    spl9_18 | ~spl9_45 | spl9_70),
% 1.39/0.55    inference(avatar_split_clause,[],[f1785,f1285,f900,f378])).
% 1.39/0.55  fof(f900,plain,(
% 1.39/0.55    spl9_45 <=> k1_xboole_0 = sK7),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 1.39/0.55  fof(f1285,plain,(
% 1.39/0.55    spl9_70 <=> k1_xboole_0 = sK6),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).
% 1.39/0.55  fof(f1785,plain,(
% 1.39/0.55    k1_xboole_0 = sK8 | (~spl9_45 | spl9_70)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1784,f1286])).
% 1.39/0.55  fof(f1286,plain,(
% 1.39/0.55    k1_xboole_0 != sK6 | spl9_70),
% 1.39/0.55    inference(avatar_component_clause,[],[f1285])).
% 1.39/0.55  fof(f1784,plain,(
% 1.39/0.55    k1_xboole_0 = sK6 | k1_xboole_0 = sK8 | ~spl9_45),
% 1.39/0.55    inference(subsumption_resolution,[],[f1783,f1761])).
% 1.39/0.55  fof(f1761,plain,(
% 1.39/0.55    v1_funct_2(sK8,sK6,k1_xboole_0) | ~spl9_45),
% 1.39/0.55    inference(backward_demodulation,[],[f59,f902])).
% 1.39/0.55  fof(f902,plain,(
% 1.39/0.55    k1_xboole_0 = sK7 | ~spl9_45),
% 1.39/0.55    inference(avatar_component_clause,[],[f900])).
% 1.39/0.55  fof(f59,plain,(
% 1.39/0.55    v1_funct_2(sK8,sK6,sK7)),
% 1.39/0.55    inference(cnf_transformation,[],[f46])).
% 1.39/0.55  fof(f1783,plain,(
% 1.39/0.55    ~v1_funct_2(sK8,sK6,k1_xboole_0) | k1_xboole_0 = sK6 | k1_xboole_0 = sK8 | ~spl9_45),
% 1.39/0.55    inference(resolution,[],[f1767,f104])).
% 1.39/0.55  fof(f104,plain,(
% 1.39/0.55    ( ! [X2,X0] : (~sP5(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 1.39/0.55    inference(equality_resolution,[],[f92])).
% 1.39/0.55  fof(f92,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP5(X0,X1,X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f54])).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP5(X0,X1,X2))),
% 1.39/0.55    inference(rectify,[],[f53])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP5(X2,X1,X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP5(X2,X1,X0))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.39/0.55  fof(f1767,plain,(
% 1.39/0.55    sP5(sK8,k1_xboole_0,sK6) | ~spl9_45),
% 1.39/0.55    inference(backward_demodulation,[],[f193,f902])).
% 1.39/0.55  fof(f193,plain,(
% 1.39/0.55    sP5(sK8,sK7,sK6)),
% 1.39/0.55    inference(resolution,[],[f99,f60])).
% 1.39/0.55  fof(f99,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP5(X2,X1,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f44])).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((sP5(X2,X1,X0) & sP4(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(definition_folding,[],[f34,f43,f42,f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(flattening,[],[f33])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f12])).
% 1.39/0.55  fof(f12,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.55  fof(f2486,plain,(
% 1.39/0.55    ~spl9_36 | ~spl9_70),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f2485])).
% 1.39/0.55  fof(f2485,plain,(
% 1.39/0.55    $false | (~spl9_36 | ~spl9_70)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2484,f105])).
% 1.39/0.55  % (27266)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.39/0.55  fof(f105,plain,(
% 1.39/0.55    ( ! [X1] : (~sP3(k1_xboole_0,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f97])).
% 1.39/0.55  fof(f97,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP3(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f57])).
% 1.39/0.55  fof(f57,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f41])).
% 1.39/0.55  fof(f2484,plain,(
% 1.39/0.55    sP3(k1_xboole_0,k1_xboole_0) | (~spl9_36 | ~spl9_70)),
% 1.39/0.55    inference(backward_demodulation,[],[f799,f1287])).
% 1.39/0.55  fof(f1287,plain,(
% 1.39/0.55    k1_xboole_0 = sK6 | ~spl9_70),
% 1.39/0.55    inference(avatar_component_clause,[],[f1285])).
% 1.39/0.55  fof(f799,plain,(
% 1.39/0.55    sP3(sK6,k1_xboole_0) | ~spl9_36),
% 1.39/0.55    inference(backward_demodulation,[],[f720,f779])).
% 1.39/0.55  fof(f779,plain,(
% 1.39/0.55    k1_xboole_0 = sK7 | ~spl9_36),
% 1.39/0.55    inference(resolution,[],[f720,f96])).
% 1.39/0.55  fof(f96,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~sP3(X0,X1) | k1_xboole_0 = X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f57])).
% 1.39/0.55  fof(f720,plain,(
% 1.39/0.55    sP3(sK6,sK7) | ~spl9_36),
% 1.39/0.55    inference(avatar_component_clause,[],[f718])).
% 1.39/0.55  fof(f718,plain,(
% 1.39/0.55    spl9_36 <=> sP3(sK6,sK7)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 1.39/0.55  fof(f2438,plain,(
% 1.39/0.55    ~spl9_1 | spl9_3 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_45 | ~spl9_72 | ~spl9_82),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f2432])).
% 1.39/0.55  fof(f2432,plain,(
% 1.39/0.55    $false | (~spl9_1 | spl9_3 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_45 | ~spl9_72 | ~spl9_82)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1894,f2431])).
% 1.39/0.55  fof(f2431,plain,(
% 1.39/0.55    ( ! [X0] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_72 | ~spl9_82)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1630,f2342])).
% 1.39/0.55  fof(f2342,plain,(
% 1.39/0.55    ( ! [X0] : (sP2(X0,k2_funct_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_82)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2341,f878])).
% 1.39/0.55  fof(f878,plain,(
% 1.39/0.55    v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl9_18 | ~spl9_20)),
% 1.39/0.55    inference(backward_demodulation,[],[f470,f380])).
% 1.39/0.55  fof(f470,plain,(
% 1.39/0.55    v1_relat_1(k2_funct_1(sK8)) | ~spl9_20),
% 1.39/0.55    inference(avatar_component_clause,[],[f469])).
% 1.39/0.55  fof(f469,plain,(
% 1.39/0.55    spl9_20 <=> v1_relat_1(k2_funct_1(sK8))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.39/0.55  fof(f2341,plain,(
% 1.39/0.55    ( ! [X0] : (sP2(X0,k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_82)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2336,f874])).
% 1.39/0.55  fof(f874,plain,(
% 1.39/0.55    v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl9_1 | ~spl9_18)),
% 1.39/0.55    inference(backward_demodulation,[],[f108,f380])).
% 1.39/0.55  fof(f108,plain,(
% 1.39/0.55    v1_funct_1(k2_funct_1(sK8)) | ~spl9_1),
% 1.39/0.55    inference(avatar_component_clause,[],[f107])).
% 1.39/0.55  fof(f107,plain,(
% 1.39/0.55    spl9_1 <=> v1_funct_1(k2_funct_1(sK8))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.39/0.55  fof(f2336,plain,(
% 1.39/0.55    ( ! [X0] : (sP2(X0,k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_82)),
% 1.39/0.55    inference(resolution,[],[f2315,f86])).
% 1.39/0.55  fof(f2315,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0)) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_82)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2314,f878])).
% 1.39/0.55  fof(f2314,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_18 | ~spl9_31 | ~spl9_82)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2313,f874])).
% 1.39/0.55  fof(f2313,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | (~spl9_18 | ~spl9_31 | ~spl9_82)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2312,f881])).
% 1.39/0.55  fof(f881,plain,(
% 1.39/0.55    v2_funct_1(k2_funct_1(k1_xboole_0)) | (~spl9_18 | ~spl9_31)),
% 1.39/0.55    inference(backward_demodulation,[],[f571,f380])).
% 1.39/0.55  fof(f571,plain,(
% 1.39/0.55    v2_funct_1(k2_funct_1(sK8)) | ~spl9_31),
% 1.39/0.55    inference(avatar_component_clause,[],[f570])).
% 1.39/0.55  fof(f570,plain,(
% 1.39/0.55    spl9_31 <=> v2_funct_1(k2_funct_1(sK8))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 1.39/0.55  fof(f2312,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0) | ~v2_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | ~spl9_82),
% 1.39/0.55    inference(resolution,[],[f2022,f231])).
% 1.39/0.55  fof(f231,plain,(
% 1.39/0.55    ( ! [X2,X3] : (~v4_relat_1(k2_funct_1(X2),X3) | r1_tarski(k2_relat_1(X2),X3) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f220,f76])).
% 1.39/0.55  % (27262)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.39/0.55  fof(f220,plain,(
% 1.39/0.55    ( ! [X2,X3] : (r1_tarski(k2_relat_1(X2),X3) | ~v4_relat_1(k2_funct_1(X2),X3) | ~v1_relat_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.39/0.55    inference(superposition,[],[f81,f78])).
% 1.39/0.55  fof(f2022,plain,(
% 1.39/0.55    ( ! [X0] : (v4_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0)),X0)) ) | ~spl9_82),
% 1.39/0.55    inference(avatar_component_clause,[],[f2021])).
% 1.39/0.55  fof(f2021,plain,(
% 1.39/0.55    spl9_82 <=> ! [X0] : v4_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0)),X0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).
% 1.39/0.55  fof(f1630,plain,(
% 1.39/0.55    ( ! [X0] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~sP2(X0,k2_funct_1(k1_xboole_0))) ) | ~spl9_72),
% 1.39/0.55    inference(avatar_component_clause,[],[f1629])).
% 1.39/0.55  fof(f1629,plain,(
% 1.39/0.55    spl9_72 <=> ! [X0] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~sP2(X0,k2_funct_1(k1_xboole_0)))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).
% 1.39/0.55  fof(f1894,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6))) | (spl9_3 | ~spl9_18 | ~spl9_45)),
% 1.39/0.55    inference(forward_demodulation,[],[f1765,f380])).
% 1.39/0.55  fof(f1765,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6))) | (spl9_3 | ~spl9_45)),
% 1.39/0.55    inference(backward_demodulation,[],[f117,f902])).
% 1.39/0.55  fof(f117,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) | spl9_3),
% 1.39/0.55    inference(avatar_component_clause,[],[f115])).
% 1.39/0.55  fof(f115,plain,(
% 1.39/0.55    spl9_3 <=> m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.39/0.55  fof(f2309,plain,(
% 1.39/0.55    spl9_72 | ~spl9_18 | ~spl9_21 | ~spl9_45),
% 1.39/0.55    inference(avatar_split_clause,[],[f2279,f900,f473,f378,f1629])).
% 1.39/0.55  fof(f473,plain,(
% 1.39/0.55    spl9_21 <=> sK7 = k1_relat_1(k2_funct_1(sK8))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.39/0.55  fof(f2279,plain,(
% 1.39/0.55    ( ! [X3] : (~sP2(X3,k2_funct_1(k1_xboole_0)) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))) ) | (~spl9_18 | ~spl9_21 | ~spl9_45)),
% 1.39/0.55    inference(forward_demodulation,[],[f2278,f380])).
% 1.39/0.55  fof(f2278,plain,(
% 1.39/0.55    ( ! [X3] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) | ~sP2(X3,k2_funct_1(sK8))) ) | (~spl9_18 | ~spl9_21 | ~spl9_45)),
% 1.39/0.55    inference(forward_demodulation,[],[f2277,f380])).
% 1.39/0.55  fof(f2277,plain,(
% 1.39/0.55    ( ! [X3] : (m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) | ~sP2(X3,k2_funct_1(sK8))) ) | (~spl9_21 | ~spl9_45)),
% 1.39/0.55    inference(forward_demodulation,[],[f526,f902])).
% 1.39/0.55  fof(f526,plain,(
% 1.39/0.55    ( ! [X3] : (m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,X3))) | ~sP2(X3,k2_funct_1(sK8))) ) | ~spl9_21),
% 1.39/0.55    inference(superposition,[],[f85,f475])).
% 1.39/0.55  fof(f475,plain,(
% 1.39/0.55    sK7 = k1_relat_1(k2_funct_1(sK8)) | ~spl9_21),
% 1.39/0.55    inference(avatar_component_clause,[],[f473])).
% 1.39/0.55  fof(f85,plain,(
% 1.39/0.55    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP2(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f2305,plain,(
% 1.39/0.55    ~spl9_1 | spl9_3 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_31 | ~spl9_45 | ~spl9_80),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f2299])).
% 1.39/0.55  fof(f2299,plain,(
% 1.39/0.55    $false | (~spl9_1 | spl9_3 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_31 | ~spl9_45 | ~spl9_80)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1894,f2280])).
% 1.39/0.55  fof(f2280,plain,(
% 1.39/0.55    ( ! [X3] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_31 | ~spl9_45 | ~spl9_80)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2279,f2232])).
% 1.39/0.55  fof(f2232,plain,(
% 1.39/0.55    ( ! [X0] : (sP2(X0,k2_funct_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_80)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2231,f878])).
% 1.39/0.55  fof(f2231,plain,(
% 1.39/0.55    ( ! [X0] : (sP2(X0,k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_80)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2230,f874])).
% 1.39/0.55  fof(f2230,plain,(
% 1.39/0.55    ( ! [X0] : (sP2(X0,k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_80)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2200,f66])).
% 1.39/0.55  fof(f66,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.55  fof(f2200,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | sP2(X0,k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_80)),
% 1.39/0.55    inference(superposition,[],[f86,f2059])).
% 1.39/0.55  fof(f2059,plain,(
% 1.39/0.55    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_80)),
% 1.39/0.55    inference(forward_demodulation,[],[f2058,f64])).
% 1.39/0.55  fof(f64,plain,(
% 1.39/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(cnf_transformation,[],[f6])).
% 1.39/0.55  fof(f6,axiom,(
% 1.39/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.39/0.55  fof(f2058,plain,(
% 1.39/0.55    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl9_1 | ~spl9_18 | ~spl9_20 | ~spl9_31 | ~spl9_80)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2057,f878])).
% 1.39/0.55  fof(f2057,plain,(
% 1.39/0.55    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl9_1 | ~spl9_18 | ~spl9_31 | ~spl9_80)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2056,f874])).
% 1.39/0.55  fof(f2056,plain,(
% 1.39/0.55    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl9_18 | ~spl9_31 | ~spl9_80)),
% 1.39/0.55    inference(subsumption_resolution,[],[f2040,f881])).
% 1.39/0.55  % (27276)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.39/0.55  fof(f2040,plain,(
% 1.39/0.55    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v2_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl9_80),
% 1.39/0.55    inference(superposition,[],[f78,f2013])).
% 1.39/0.55  fof(f2013,plain,(
% 1.39/0.55    k1_xboole_0 = k2_funct_1(k2_funct_1(k1_xboole_0)) | ~spl9_80),
% 1.39/0.55    inference(avatar_component_clause,[],[f2011])).
% 1.39/0.55  fof(f2011,plain,(
% 1.39/0.55    spl9_80 <=> k1_xboole_0 = k2_funct_1(k2_funct_1(k1_xboole_0))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).
% 1.39/0.55  fof(f2023,plain,(
% 1.39/0.55    spl9_82 | spl9_80 | ~spl9_18 | ~spl9_32 | ~spl9_36),
% 1.39/0.55    inference(avatar_split_clause,[],[f1999,f718,f574,f378,f2011,f2021])).
% 1.39/0.55  fof(f574,plain,(
% 1.39/0.55    spl9_32 <=> sP2(sK7,k2_funct_1(k2_funct_1(sK8)))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 1.39/0.55  fof(f1999,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k2_funct_1(k2_funct_1(k1_xboole_0)) | v4_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0)),X0)) ) | (~spl9_18 | ~spl9_32 | ~spl9_36)),
% 1.39/0.55    inference(resolution,[],[f1892,f369])).
% 1.39/0.55  fof(f369,plain,(
% 1.39/0.55    ( ! [X4,X5] : (~sP2(k1_xboole_0,X4) | k1_xboole_0 = X4 | v4_relat_1(X4,X5)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f368,f183])).
% 1.39/0.55  fof(f183,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~sP2(X0,X1) | v1_relat_1(X1)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f180,f80])).
% 1.39/0.55  fof(f180,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~sP2(X0,X1) | v1_relat_1(X1) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(X1),X0))) )),
% 1.39/0.55    inference(resolution,[],[f85,f67])).
% 1.39/0.55  fof(f368,plain,(
% 1.39/0.55    ( ! [X4,X5] : (v4_relat_1(X4,X5) | ~v1_relat_1(X4) | k1_xboole_0 = X4 | ~sP2(k1_xboole_0,X4)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f354,f66])).
% 1.39/0.55  fof(f354,plain,(
% 1.39/0.55    ( ! [X4,X5] : (~r1_tarski(k1_xboole_0,X5) | v4_relat_1(X4,X5) | ~v1_relat_1(X4) | k1_xboole_0 = X4 | ~sP2(k1_xboole_0,X4)) )),
% 1.39/0.55    inference(superposition,[],[f82,f349])).
% 1.39/0.55  fof(f349,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 = X0 | ~sP2(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f346,f84])).
% 1.39/0.55  fof(f346,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(X0),k1_xboole_0) | k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 = X0 | ~sP2(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(resolution,[],[f104,f195])).
% 1.39/0.55  fof(f195,plain,(
% 1.39/0.55    ( ! [X2,X1] : (sP5(X1,X2,k1_relat_1(X1)) | ~sP2(X2,X1)) )),
% 1.39/0.55    inference(resolution,[],[f99,f85])).
% 1.39/0.55  fof(f82,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f49])).
% 1.39/0.55  fof(f1892,plain,(
% 1.39/0.55    sP2(k1_xboole_0,k2_funct_1(k2_funct_1(k1_xboole_0))) | (~spl9_18 | ~spl9_32 | ~spl9_36)),
% 1.39/0.55    inference(forward_demodulation,[],[f797,f380])).
% 1.39/0.55  fof(f797,plain,(
% 1.39/0.55    sP2(k1_xboole_0,k2_funct_1(k2_funct_1(sK8))) | (~spl9_32 | ~spl9_36)),
% 1.39/0.55    inference(backward_demodulation,[],[f576,f779])).
% 1.39/0.55  fof(f576,plain,(
% 1.39/0.55    sP2(sK7,k2_funct_1(k2_funct_1(sK8))) | ~spl9_32),
% 1.39/0.55    inference(avatar_component_clause,[],[f574])).
% 1.39/0.55  fof(f1878,plain,(
% 1.39/0.55    spl9_6 | ~spl9_18 | ~spl9_45),
% 1.39/0.55    inference(avatar_split_clause,[],[f1877,f900,f378,f144])).
% 1.39/0.55  fof(f144,plain,(
% 1.39/0.55    spl9_6 <=> v1_relat_1(k1_xboole_0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.39/0.55  fof(f1877,plain,(
% 1.39/0.55    v1_relat_1(k1_xboole_0) | (~spl9_18 | ~spl9_45)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1876,f80])).
% 1.39/0.55  fof(f1876,plain,(
% 1.39/0.55    v1_relat_1(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(sK6,k1_xboole_0)) | (~spl9_18 | ~spl9_45)),
% 1.39/0.55    inference(resolution,[],[f1849,f67])).
% 1.39/0.55  fof(f1849,plain,(
% 1.39/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) | (~spl9_18 | ~spl9_45)),
% 1.39/0.55    inference(forward_demodulation,[],[f1762,f380])).
% 1.39/0.55  fof(f1762,plain,(
% 1.39/0.55    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) | ~spl9_45),
% 1.39/0.55    inference(backward_demodulation,[],[f60,f902])).
% 1.39/0.55  fof(f1747,plain,(
% 1.39/0.55    spl9_45 | ~spl9_36),
% 1.39/0.55    inference(avatar_split_clause,[],[f1746,f718,f900])).
% 1.39/0.55  fof(f1746,plain,(
% 1.39/0.55    k1_xboole_0 = sK7 | ~spl9_36),
% 1.39/0.55    inference(resolution,[],[f720,f96])).
% 1.39/0.55  fof(f1726,plain,(
% 1.39/0.55    spl9_35 | spl9_36),
% 1.39/0.55    inference(avatar_split_clause,[],[f1000,f718,f714])).
% 1.39/0.55  fof(f714,plain,(
% 1.39/0.55    spl9_35 <=> sK6 = k1_relat_1(sK8)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 1.39/0.55  fof(f1000,plain,(
% 1.39/0.55    sP3(sK6,sK7) | sK6 = k1_relat_1(sK8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f996,f59])).
% 1.39/0.55  fof(f996,plain,(
% 1.39/0.55    ~v1_funct_2(sK8,sK6,sK7) | sP3(sK6,sK7) | sK6 = k1_relat_1(sK8)),
% 1.39/0.55    inference(resolution,[],[f60,f396])).
% 1.39/0.55  fof(f396,plain,(
% 1.39/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP3(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f394,f98])).
% 1.39/0.55  fof(f98,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X0,X2,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f44])).
% 1.39/0.55  fof(f394,plain,(
% 1.39/0.55    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP3(X3,X4) | ~sP4(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.39/0.55    inference(superposition,[],[f94,f91])).
% 1.39/0.55  fof(f91,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f32])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.55  fof(f94,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP3(X0,X2) | ~sP4(X0,X1,X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f56])).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP3(X0,X2) | ~sP4(X0,X1,X2))),
% 1.39/0.55    inference(rectify,[],[f55])).
% 1.39/0.55  fof(f55,plain,(
% 1.39/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f42])).
% 1.39/0.55  fof(f1696,plain,(
% 1.39/0.55    spl9_3 | ~spl9_21 | ~spl9_26 | ~spl9_35),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f1695])).
% 1.39/0.55  fof(f1695,plain,(
% 1.39/0.55    $false | (spl9_3 | ~spl9_21 | ~spl9_26 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1694,f117])).
% 1.39/0.55  fof(f1694,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) | (~spl9_21 | ~spl9_26 | ~spl9_35)),
% 1.39/0.55    inference(forward_demodulation,[],[f1693,f475])).
% 1.39/0.55  fof(f1693,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6))) | (~spl9_26 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1692,f127])).
% 1.39/0.55  fof(f1692,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6))) | ~v1_relat_1(sK8) | (~spl9_26 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1691,f58])).
% 1.39/0.55  fof(f1691,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6))) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_26 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1690,f61])).
% 1.39/0.55  fof(f1690,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6))) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_26 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1670,f542])).
% 1.39/0.55  fof(f542,plain,(
% 1.39/0.55    sP1(k2_funct_1(sK8)) | ~spl9_26),
% 1.39/0.55    inference(avatar_component_clause,[],[f541])).
% 1.39/0.55  fof(f541,plain,(
% 1.39/0.55    spl9_26 <=> sP1(k2_funct_1(sK8))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.39/0.55  fof(f1670,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK8)),sK6))) | ~sP1(k2_funct_1(sK8)) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_35),
% 1.39/0.55    inference(superposition,[],[f236,f716])).
% 1.39/0.55  fof(f716,plain,(
% 1.39/0.55    sK6 = k1_relat_1(sK8) | ~spl9_35),
% 1.39/0.55    inference(avatar_component_clause,[],[f714])).
% 1.39/0.55  fof(f236,plain,(
% 1.39/0.55    ( ! [X1] : (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1)))) | ~sP1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.39/0.55    inference(superposition,[],[f74,f79])).
% 1.39/0.55  fof(f74,plain,(
% 1.39/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~sP1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP1(X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP1(X0))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.39/0.55  fof(f1502,plain,(
% 1.39/0.55    spl9_32 | ~spl9_1 | ~spl9_20 | ~spl9_21 | ~spl9_31),
% 1.39/0.55    inference(avatar_split_clause,[],[f1501,f570,f473,f469,f107,f574])).
% 1.39/0.55  fof(f1501,plain,(
% 1.39/0.55    sP2(sK7,k2_funct_1(k2_funct_1(sK8))) | (~spl9_1 | ~spl9_20 | ~spl9_21 | ~spl9_31)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1500,f470])).
% 1.39/0.55  fof(f1500,plain,(
% 1.39/0.55    sP2(sK7,k2_funct_1(k2_funct_1(sK8))) | ~v1_relat_1(k2_funct_1(sK8)) | (~spl9_1 | ~spl9_21 | ~spl9_31)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1499,f108])).
% 1.39/0.55  fof(f1499,plain,(
% 1.39/0.55    sP2(sK7,k2_funct_1(k2_funct_1(sK8))) | ~v1_funct_1(k2_funct_1(sK8)) | ~v1_relat_1(k2_funct_1(sK8)) | (~spl9_21 | ~spl9_31)),
% 1.39/0.55    inference(subsumption_resolution,[],[f1472,f571])).
% 1.39/0.55  fof(f1472,plain,(
% 1.39/0.55    sP2(sK7,k2_funct_1(k2_funct_1(sK8))) | ~v2_funct_1(k2_funct_1(sK8)) | ~v1_funct_1(k2_funct_1(sK8)) | ~v1_relat_1(k2_funct_1(sK8)) | ~spl9_21),
% 1.39/0.55    inference(superposition,[],[f246,f475])).
% 1.39/0.55  fof(f246,plain,(
% 1.39/0.55    ( ! [X8] : (sP2(k1_relat_1(X8),k2_funct_1(X8)) | ~v2_funct_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f245,f76])).
% 1.39/0.55  fof(f245,plain,(
% 1.39/0.55    ( ! [X8] : (sP2(k1_relat_1(X8),k2_funct_1(X8)) | ~v1_relat_1(k2_funct_1(X8)) | ~v2_funct_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f242,f77])).
% 1.39/0.55  fof(f242,plain,(
% 1.39/0.55    ( ! [X8] : (sP2(k1_relat_1(X8),k2_funct_1(X8)) | ~v1_funct_1(k2_funct_1(X8)) | ~v1_relat_1(k2_funct_1(X8)) | ~v2_funct_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 1.39/0.55    inference(superposition,[],[f208,f79])).
% 1.39/0.55  fof(f208,plain,(
% 1.39/0.55    ( ! [X0] : (sP2(k2_relat_1(X0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(resolution,[],[f86,f100])).
% 1.39/0.55  fof(f100,plain,(
% 1.39/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f88])).
% 1.39/0.55  fof(f88,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f52])).
% 1.39/0.55  fof(f52,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(flattening,[],[f51])).
% 1.39/0.55  fof(f51,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.55  fof(f1410,plain,(
% 1.39/0.55    spl9_21 | ~spl9_20),
% 1.39/0.55    inference(avatar_split_clause,[],[f1409,f469,f473])).
% 1.39/0.55  fof(f1409,plain,(
% 1.39/0.55    sK7 = k1_relat_1(k2_funct_1(sK8)) | ~spl9_20),
% 1.39/0.55    inference(subsumption_resolution,[],[f1408,f470])).
% 1.39/0.55  fof(f1408,plain,(
% 1.39/0.55    sK7 = k1_relat_1(k2_funct_1(sK8)) | ~v1_relat_1(k2_funct_1(sK8))),
% 1.39/0.55    inference(subsumption_resolution,[],[f1403,f321])).
% 1.39/0.55  fof(f321,plain,(
% 1.39/0.55    v4_relat_1(k2_funct_1(sK8),sK7)),
% 1.39/0.55    inference(subsumption_resolution,[],[f320,f127])).
% 1.39/0.55  fof(f320,plain,(
% 1.39/0.55    v4_relat_1(k2_funct_1(sK8),sK7) | ~v1_relat_1(sK8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f319,f58])).
% 1.39/0.55  fof(f319,plain,(
% 1.39/0.55    v4_relat_1(k2_funct_1(sK8),sK7) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f275,f61])).
% 1.39/0.55  fof(f275,plain,(
% 1.39/0.55    v4_relat_1(k2_funct_1(sK8),sK7) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8)),
% 1.39/0.55    inference(superposition,[],[f233,f265])).
% 1.39/0.55  fof(f233,plain,(
% 1.39/0.55    ( ! [X10] : (v4_relat_1(k2_funct_1(X10),k2_relat_1(X10)) | ~v2_funct_1(X10) | ~v1_funct_1(X10) | ~v1_relat_1(X10)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f224,f76])).
% 1.39/0.55  fof(f224,plain,(
% 1.39/0.55    ( ! [X10] : (v4_relat_1(k2_funct_1(X10),k2_relat_1(X10)) | ~v1_relat_1(k2_funct_1(X10)) | ~v2_funct_1(X10) | ~v1_funct_1(X10) | ~v1_relat_1(X10)) )),
% 1.39/0.55    inference(superposition,[],[f154,f78])).
% 1.39/0.55  fof(f154,plain,(
% 1.39/0.55    ( ! [X0] : (v4_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(resolution,[],[f82,f100])).
% 1.39/0.55  fof(f1403,plain,(
% 1.39/0.55    sK7 = k1_relat_1(k2_funct_1(sK8)) | ~v4_relat_1(k2_funct_1(sK8),sK7) | ~v1_relat_1(k2_funct_1(sK8))),
% 1.39/0.55    inference(resolution,[],[f990,f160])).
% 1.39/0.55  fof(f160,plain,(
% 1.39/0.55    ( ! [X2,X3] : (~r1_tarski(X2,k1_relat_1(X3)) | k1_relat_1(X3) = X2 | ~v4_relat_1(X3,X2) | ~v1_relat_1(X3)) )),
% 1.39/0.55    inference(resolution,[],[f89,f81])).
% 1.39/0.55  fof(f89,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f52])).
% 1.39/0.55  fof(f990,plain,(
% 1.39/0.55    r1_tarski(sK7,k1_relat_1(k2_funct_1(sK8)))),
% 1.39/0.55    inference(subsumption_resolution,[],[f989,f127])).
% 1.39/0.55  fof(f989,plain,(
% 1.39/0.55    r1_tarski(sK7,k1_relat_1(k2_funct_1(sK8))) | ~v1_relat_1(sK8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f988,f58])).
% 1.39/0.55  fof(f988,plain,(
% 1.39/0.55    r1_tarski(sK7,k1_relat_1(k2_funct_1(sK8))) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f955,f61])).
% 1.39/0.55  fof(f955,plain,(
% 1.39/0.55    r1_tarski(sK7,k1_relat_1(k2_funct_1(sK8))) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8)),
% 1.39/0.55    inference(superposition,[],[f442,f265])).
% 1.39/0.55  fof(f442,plain,(
% 1.39/0.55    ( ! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f435,f76])).
% 1.39/0.55  fof(f435,plain,(
% 1.39/0.55    ( ! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X1))) )),
% 1.39/0.55    inference(resolution,[],[f231,f154])).
% 1.39/0.55  fof(f1281,plain,(
% 1.39/0.55    ~spl9_6 | spl9_69),
% 1.39/0.55    inference(avatar_split_clause,[],[f1277,f1279,f144])).
% 1.39/0.55  fof(f1277,plain,(
% 1.39/0.55    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f156,f66])).
% 1.39/0.55  fof(f156,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v4_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.39/0.55    inference(superposition,[],[f82,f64])).
% 1.39/0.55  fof(f778,plain,(
% 1.39/0.55    spl9_2 | ~spl9_35),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f777])).
% 1.39/0.55  fof(f777,plain,(
% 1.39/0.55    $false | (spl9_2 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f776,f127])).
% 1.39/0.55  fof(f776,plain,(
% 1.39/0.55    ~v1_relat_1(sK8) | (spl9_2 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f775,f58])).
% 1.39/0.55  fof(f775,plain,(
% 1.39/0.55    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (spl9_2 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f774,f61])).
% 1.39/0.55  fof(f774,plain,(
% 1.39/0.55    ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (spl9_2 | ~spl9_35)),
% 1.39/0.55    inference(subsumption_resolution,[],[f747,f641])).
% 1.39/0.55  fof(f747,plain,(
% 1.39/0.55    sP2(sK6,k2_funct_1(sK8)) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_35),
% 1.39/0.55    inference(superposition,[],[f246,f716])).
% 1.39/0.55  fof(f598,plain,(
% 1.39/0.55    spl9_31),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f597])).
% 1.39/0.55  fof(f597,plain,(
% 1.39/0.55    $false | spl9_31),
% 1.39/0.55    inference(subsumption_resolution,[],[f596,f127])).
% 1.39/0.55  fof(f596,plain,(
% 1.39/0.55    ~v1_relat_1(sK8) | spl9_31),
% 1.39/0.55    inference(subsumption_resolution,[],[f595,f58])).
% 1.39/0.55  fof(f595,plain,(
% 1.39/0.55    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_31),
% 1.39/0.55    inference(subsumption_resolution,[],[f594,f61])).
% 1.39/0.55  fof(f594,plain,(
% 1.39/0.55    ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_31),
% 1.39/0.55    inference(resolution,[],[f593,f71])).
% 1.39/0.55  fof(f71,plain,(
% 1.39/0.55    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(definition_folding,[],[f21,f35])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f20])).
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.39/0.55  fof(f593,plain,(
% 1.39/0.55    ~sP0(sK8) | spl9_31),
% 1.39/0.55    inference(resolution,[],[f572,f70])).
% 1.39/0.55  fof(f70,plain,(
% 1.39/0.55    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f47])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f35])).
% 1.39/0.55  fof(f572,plain,(
% 1.39/0.55    ~v2_funct_1(k2_funct_1(sK8)) | spl9_31),
% 1.39/0.55    inference(avatar_component_clause,[],[f570])).
% 1.39/0.55  fof(f590,plain,(
% 1.39/0.55    ~spl9_1 | ~spl9_20 | spl9_26),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f589])).
% 1.39/0.55  fof(f589,plain,(
% 1.39/0.55    $false | (~spl9_1 | ~spl9_20 | spl9_26)),
% 1.39/0.55    inference(subsumption_resolution,[],[f588,f470])).
% 1.39/0.55  fof(f588,plain,(
% 1.39/0.55    ~v1_relat_1(k2_funct_1(sK8)) | (~spl9_1 | spl9_26)),
% 1.39/0.55    inference(subsumption_resolution,[],[f587,f108])).
% 1.39/0.55  fof(f587,plain,(
% 1.39/0.55    ~v1_funct_1(k2_funct_1(sK8)) | ~v1_relat_1(k2_funct_1(sK8)) | spl9_26),
% 1.39/0.55    inference(resolution,[],[f543,f75])).
% 1.39/0.55  fof(f75,plain,(
% 1.39/0.55    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(definition_folding,[],[f23,f37])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f22])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,axiom,(
% 1.39/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.39/0.55  fof(f543,plain,(
% 1.39/0.55    ~sP1(k2_funct_1(sK8)) | spl9_26),
% 1.39/0.55    inference(avatar_component_clause,[],[f541])).
% 1.39/0.55  fof(f506,plain,(
% 1.39/0.55    spl9_20),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f505])).
% 1.39/0.55  fof(f505,plain,(
% 1.39/0.55    $false | spl9_20),
% 1.39/0.55    inference(subsumption_resolution,[],[f504,f127])).
% 1.39/0.55  fof(f504,plain,(
% 1.39/0.55    ~v1_relat_1(sK8) | spl9_20),
% 1.39/0.55    inference(subsumption_resolution,[],[f502,f58])).
% 1.39/0.55  fof(f502,plain,(
% 1.39/0.55    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_20),
% 1.39/0.55    inference(resolution,[],[f471,f76])).
% 1.39/0.55  fof(f471,plain,(
% 1.39/0.55    ~v1_relat_1(k2_funct_1(sK8)) | spl9_20),
% 1.39/0.55    inference(avatar_component_clause,[],[f469])).
% 1.39/0.55  fof(f126,plain,(
% 1.39/0.55    spl9_1),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f125])).
% 1.39/0.55  fof(f125,plain,(
% 1.39/0.55    $false | spl9_1),
% 1.39/0.55    inference(subsumption_resolution,[],[f124,f80])).
% 1.39/0.55  fof(f124,plain,(
% 1.39/0.55    ~v1_relat_1(k2_zfmisc_1(sK6,sK7)) | spl9_1),
% 1.39/0.55    inference(subsumption_resolution,[],[f123,f122])).
% 1.39/0.55  fof(f122,plain,(
% 1.39/0.55    ~v1_relat_1(sK8) | spl9_1),
% 1.39/0.55    inference(subsumption_resolution,[],[f121,f58])).
% 1.39/0.55  fof(f121,plain,(
% 1.39/0.55    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_1),
% 1.39/0.55    inference(resolution,[],[f77,f109])).
% 1.39/0.55  fof(f109,plain,(
% 1.39/0.55    ~v1_funct_1(k2_funct_1(sK8)) | spl9_1),
% 1.39/0.55    inference(avatar_component_clause,[],[f107])).
% 1.39/0.55  fof(f118,plain,(
% 1.39/0.55    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 1.39/0.55    inference(avatar_split_clause,[],[f63,f115,f111,f107])).
% 1.39/0.55  fof(f63,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) | ~v1_funct_2(k2_funct_1(sK8),sK7,sK6) | ~v1_funct_1(k2_funct_1(sK8))),
% 1.39/0.55    inference(cnf_transformation,[],[f46])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (27256)------------------------------
% 1.39/0.55  % (27256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (27256)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (27256)Memory used [KB]: 7036
% 1.39/0.55  % (27256)Time elapsed: 0.101 s
% 1.39/0.55  % (27256)------------------------------
% 1.39/0.55  % (27256)------------------------------
% 1.39/0.55  % (27277)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.39/0.55  % (27251)Success in time 0.186 s
%------------------------------------------------------------------------------
