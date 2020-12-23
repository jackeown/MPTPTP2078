%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 526 expanded)
%              Number of leaves         :   24 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :  556 (2850 expanded)
%              Number of equality atoms :  121 ( 473 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f603,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f126,f196,f346,f353,f362,f406,f454,f602])).

fof(f602,plain,
    ( spl4_3
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f600,f105])).

fof(f105,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f600,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f599,f466])).

fof(f466,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f462,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f462,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_15 ),
    inference(superposition,[],[f361,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f361,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl4_15
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f599,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f598,f122])).

fof(f122,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f79,f50])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f598,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f597,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f597,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f588,f51])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f588,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f483,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f483,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f482,f122])).

fof(f482,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f481,f48])).

fof(f481,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f475,f51])).

fof(f475,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f157,f181])).

fof(f181,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f179,f50])).

fof(f179,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f80,f52])).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f157,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f156,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f156,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f153,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f153,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f63,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f454,plain,
    ( spl4_3
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f452,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f452,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK0))
    | spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f429,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f88,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f88,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f429,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f105,f352])).

fof(f352,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl4_13
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f406,plain,
    ( spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f404,f176])).

fof(f176,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f175,f56])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f174,f55])).

fof(f55,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f174,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f173,f57])).

fof(f57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f173,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f171,f58])).

fof(f58,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

fof(f171,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f70,f54])).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f404,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f403,f384])).

fof(f384,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f383,f57])).

fof(f383,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f382,f58])).

fof(f382,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f334,f366])).

fof(f366,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f51,f192])).

fof(f192,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f334,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f331])).

fof(f331,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f168,f54])).

fof(f168,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_relat_1(X2)
      | k1_xboole_0 = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f163,f64])).

fof(f163,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_relat_1(X2)
      | k1_xboole_0 = k2_funct_1(X2)
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f60,f67])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f403,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f368,f357])).

fof(f357,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f368,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0)
    | spl4_2
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f102,f192])).

fof(f102,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f362,plain,
    ( spl4_15
    | spl4_7 ),
    inference(avatar_split_clause,[],[f234,f194,f360])).

fof(f234,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f227,f49])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f227,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f82,f50])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f353,plain,
    ( spl4_13
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f349,f194,f351])).

fof(f349,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f348,f122])).

fof(f348,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f347,f48])).

fof(f347,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f317,f51])).

fof(f317,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f160,f181])).

fof(f160,plain,(
    ! [X2] :
      ( k1_xboole_0 != k2_relat_1(X2)
      | k1_xboole_0 = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f155,f64])).

fof(f155,plain,(
    ! [X2] :
      ( k1_xboole_0 != k2_relat_1(X2)
      | k1_xboole_0 = k2_funct_1(X2)
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f59,f66])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f346,plain,
    ( spl4_2
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl4_2
    | spl4_7 ),
    inference(subsumption_resolution,[],[f344,f102])).

fof(f344,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_7 ),
    inference(forward_demodulation,[],[f343,f242])).

fof(f242,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f240,f50])).

fof(f240,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_7 ),
    inference(superposition,[],[f235,f81])).

fof(f235,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f234,f195])).

fof(f195,plain,
    ( k1_xboole_0 != sK1
    | spl4_7 ),
    inference(avatar_component_clause,[],[f194])).

fof(f343,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f342,f122])).

fof(f342,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f341,f48])).

fof(f341,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f340,f51])).

fof(f340,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f314,f67])).

fof(f314,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f313,f122])).

fof(f313,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f312,f48])).

fof(f312,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f298,f51])).

fof(f298,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f159,f181])).

fof(f159,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f158,f64])).

fof(f158,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f154,f65])).

fof(f154,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f62,f66])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f196,plain,
    ( spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f189,f194,f191])).

fof(f189,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f184,f122])).

fof(f184,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f60,f181])).

fof(f126,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f122,f119])).

fof(f119,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f118,f48])).

fof(f118,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f65,f99])).

fof(f99,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f106,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f104,f101,f98])).

fof(f53,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (3893)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (3893)Refutation not found, incomplete strategy% (3893)------------------------------
% 0.20/0.45  % (3893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (3893)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (3893)Memory used [KB]: 10618
% 0.20/0.45  % (3893)Time elapsed: 0.042 s
% 0.20/0.45  % (3893)------------------------------
% 0.20/0.45  % (3893)------------------------------
% 0.20/0.45  % (3888)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.45  % (3875)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (3875)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f603,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f106,f126,f196,f346,f353,f362,f406,f454,f602])).
% 0.20/0.47  fof(f602,plain,(
% 0.20/0.47    spl4_3 | ~spl4_15),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f601])).
% 0.20/0.47  fof(f601,plain,(
% 0.20/0.47    $false | (spl4_3 | ~spl4_15)),
% 0.20/0.47    inference(subsumption_resolution,[],[f600,f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl4_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f600,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_15),
% 0.20/0.47    inference(forward_demodulation,[],[f599,f466])).
% 0.20/0.47  fof(f466,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2) | ~spl4_15),
% 0.20/0.47    inference(subsumption_resolution,[],[f462,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f16])).
% 0.20/0.47  fof(f16,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.47  fof(f462,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_15),
% 0.20/0.47    inference(superposition,[],[f361,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f361,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f360])).
% 0.20/0.47  fof(f360,plain,(
% 0.20/0.47    spl4_15 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.47  fof(f599,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.20/0.47    inference(subsumption_resolution,[],[f598,f122])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f79,f50])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.47  fof(f598,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f597,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f597,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f588,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    v2_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f588,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(superposition,[],[f483,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.47  fof(f483,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))),
% 0.20/0.47    inference(subsumption_resolution,[],[f482,f122])).
% 0.20/0.47  fof(f482,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f481,f48])).
% 0.20/0.47  fof(f481,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f475,f51])).
% 0.20/0.47  fof(f475,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(superposition,[],[f157,f181])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    sK1 = k2_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f179,f50])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(superposition,[],[f80,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f156,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f153,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(superposition,[],[f63,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.47  fof(f454,plain,(
% 0.20/0.47    spl4_3 | ~spl4_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f453])).
% 0.20/0.47  fof(f453,plain,(
% 0.20/0.47    $false | (spl4_3 | ~spl4_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f452,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f452,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK0)) | (spl4_3 | ~spl4_13)),
% 0.20/0.47    inference(resolution,[],[f429,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f88,f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.47    inference(rectify,[],[f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.47  fof(f429,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl4_3 | ~spl4_13)),
% 0.20/0.47    inference(backward_demodulation,[],[f105,f352])).
% 0.20/0.47  fof(f352,plain,(
% 0.20/0.47    k1_xboole_0 = k2_funct_1(sK2) | ~spl4_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f351])).
% 0.20/0.47  fof(f351,plain,(
% 0.20/0.47    spl4_13 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.47  fof(f406,plain,(
% 0.20/0.47    spl4_2 | ~spl4_6 | ~spl4_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f405])).
% 0.20/0.47  fof(f405,plain,(
% 0.20/0.47    $false | (spl4_2 | ~spl4_6 | ~spl4_7)),
% 0.20/0.47    inference(subsumption_resolution,[],[f404,f176])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f175,f56])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f174,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f173,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    v1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(rectify,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f171,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    v1_funct_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f40])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(superposition,[],[f70,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.47  fof(f404,plain,(
% 0.20/0.47    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl4_2 | ~spl4_6 | ~spl4_7)),
% 0.20/0.47    inference(forward_demodulation,[],[f403,f384])).
% 0.20/0.47  fof(f384,plain,(
% 0.20/0.47    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl4_6),
% 0.20/0.47    inference(subsumption_resolution,[],[f383,f57])).
% 0.20/0.47  fof(f383,plain,(
% 0.20/0.47    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_6),
% 0.20/0.47    inference(subsumption_resolution,[],[f382,f58])).
% 0.20/0.47  fof(f382,plain,(
% 0.20/0.47    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_6),
% 0.20/0.47    inference(subsumption_resolution,[],[f334,f366])).
% 0.20/0.47  fof(f366,plain,(
% 0.20/0.47    v2_funct_1(k1_xboole_0) | ~spl4_6),
% 0.20/0.47    inference(backward_demodulation,[],[f51,f192])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | ~spl4_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f191])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    spl4_6 <=> k1_xboole_0 = sK2),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f334,plain,(
% 0.20/0.47    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f331])).
% 0.20/0.47  fof(f331,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(superposition,[],[f168,f54])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ( ! [X2] : (k1_xboole_0 != k1_relat_1(X2) | k1_xboole_0 = k2_funct_1(X2) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f163,f64])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ( ! [X2] : (k1_xboole_0 != k1_relat_1(X2) | k1_xboole_0 = k2_funct_1(X2) | ~v1_relat_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(superposition,[],[f60,f67])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.47  fof(f403,plain,(
% 0.20/0.47    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_6 | ~spl4_7)),
% 0.20/0.47    inference(forward_demodulation,[],[f368,f357])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl4_7 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f368,plain,(
% 0.20/0.47    ~v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0) | (spl4_2 | ~spl4_6)),
% 0.20/0.47    inference(backward_demodulation,[],[f102,f192])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f101])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f362,plain,(
% 0.20/0.47    spl4_15 | spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f234,f194,f360])).
% 0.20/0.47  fof(f234,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f227,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.47    inference(resolution,[],[f82,f50])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f353,plain,(
% 0.20/0.47    spl4_13 | ~spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f349,f194,f351])).
% 0.20/0.47  fof(f349,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f348,f122])).
% 0.20/0.47  fof(f348,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f347,f48])).
% 0.20/0.47  fof(f347,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f317,f51])).
% 0.20/0.47  fof(f317,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(superposition,[],[f160,f181])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    ( ! [X2] : (k1_xboole_0 != k2_relat_1(X2) | k1_xboole_0 = k2_funct_1(X2) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f155,f64])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    ( ! [X2] : (k1_xboole_0 != k2_relat_1(X2) | k1_xboole_0 = k2_funct_1(X2) | ~v1_relat_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(superposition,[],[f59,f66])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f346,plain,(
% 0.20/0.47    spl4_2 | spl4_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f345])).
% 0.20/0.47  fof(f345,plain,(
% 0.20/0.47    $false | (spl4_2 | spl4_7)),
% 0.20/0.47    inference(subsumption_resolution,[],[f344,f102])).
% 0.20/0.47  fof(f344,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_7),
% 0.20/0.47    inference(forward_demodulation,[],[f343,f242])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2) | spl4_7),
% 0.20/0.47    inference(subsumption_resolution,[],[f240,f50])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_7),
% 0.20/0.47    inference(superposition,[],[f235,f81])).
% 0.20/0.47  fof(f235,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK2) | spl4_7),
% 0.20/0.47    inference(subsumption_resolution,[],[f234,f195])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f194])).
% 0.20/0.47  fof(f343,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f342,f122])).
% 0.20/0.47  fof(f342,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f341,f48])).
% 0.20/0.47  fof(f341,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f340,f51])).
% 0.20/0.47  fof(f340,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(superposition,[],[f314,f67])).
% 0.20/0.47  fof(f314,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))),
% 0.20/0.47    inference(subsumption_resolution,[],[f313,f122])).
% 0.20/0.47  fof(f313,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f312,f48])).
% 0.20/0.47  fof(f312,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f298,f51])).
% 0.20/0.47  fof(f298,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(superposition,[],[f159,f181])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f158,f64])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f154,f65])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(superposition,[],[f62,f66])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    spl4_6 | ~spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f189,f194,f191])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 0.20/0.47    inference(subsumption_resolution,[],[f184,f122])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(superposition,[],[f60,f181])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl4_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    $false | spl4_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f122,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | spl4_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f118,f48])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 0.20/0.47    inference(resolution,[],[f65,f99])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ~v1_funct_1(k2_funct_1(sK2)) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl4_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f53,f104,f101,f98])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (3875)------------------------------
% 0.20/0.47  % (3875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3875)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (3875)Memory used [KB]: 10874
% 0.20/0.47  % (3875)Time elapsed: 0.076 s
% 0.20/0.47  % (3875)------------------------------
% 0.20/0.47  % (3875)------------------------------
% 0.20/0.47  % (3872)Success in time 0.119 s
%------------------------------------------------------------------------------
