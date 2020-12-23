%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 (22433 expanded)
%              Number of leaves         :    9 (4297 expanded)
%              Depth                    :   37
%              Number of atoms          :  267 (119099 expanded)
%              Number of equality atoms :  102 (35235 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(subsumption_resolution,[],[f290,f280])).

fof(f280,plain,(
    ! [X2] : m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) ),
    inference(resolution,[],[f258,f75])).

fof(f75,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f37,f72])).

fof(f72,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f37,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f257,f71])).

fof(f71,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f256,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f57,f236])).

fof(f236,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f225,f235])).

fof(f235,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f232,f224])).

fof(f224,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f213,f221])).

fof(f221,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f33,f211])).

fof(f211,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f148,f166,f210])).

fof(f210,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f102,f168])).

fof(f168,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f152,f48])).

fof(f152,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f78,f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f144,f130])).

fof(f130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f126,f75])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f109,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f109,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f108,f71])).

fof(f108,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f57,f100])).

fof(f100,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f69,f70])).

fof(f70,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f36,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f68,f36])).

fof(f68,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f144,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f143,f65])).

fof(f65,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f32,f34])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f143,plain,
    ( v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f142,f100])).

fof(f142,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f134,f131])).

fof(f131,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f130,f56])).

fof(f134,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f130,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f102,plain,
    ( v1_funct_2(sK3,sK0,k2_relat_1(sK3))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f85,f100])).

fof(f85,plain,(
    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(resolution,[],[f66,f71])).

fof(f66,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(resolution,[],[f34,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

% (19409)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f166,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f130,f147])).

fof(f148,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f65,f147])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f213,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f36,f211])).

fof(f232,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f223,f60])).

fof(f60,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f223,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f212,f221])).

fof(f212,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f211])).

fof(f225,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f214,f221])).

fof(f214,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f70,f211])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f290,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(resolution,[],[f289,f230])).

fof(f230,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(forward_demodulation,[],[f222,f221])).

fof(f222,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f65,f221])).

fof(f289,plain,(
    v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f285,f287])).

fof(f287,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(X0,sK2,sK3) ),
    inference(forward_demodulation,[],[f281,f236])).

fof(f281,plain,(
    ! [X0] : k1_relat_1(sK3) = k1_relset_1(X0,sK2,sK3) ),
    inference(resolution,[],[f280,f56])).

fof(f285,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(resolution,[],[f280,f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:51:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.49  % (19422)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.49  % (19411)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (19411)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f290,f280])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    ( ! [X2] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))) )),
% 0.22/0.50    inference(resolution,[],[f258,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.22/0.50    inference(backward_demodulation,[],[f37,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f36,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.50    inference(negated_conjecture,[],[f17])).
% 0.22/0.50  fof(f17,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f257,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    v1_relat_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f36,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f256,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(superposition,[],[f57,f236])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(sK3)),
% 0.22/0.50    inference(backward_demodulation,[],[f225,f235])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f232,f224])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.50    inference(backward_demodulation,[],[f213,f221])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    k1_xboole_0 = sK0),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f220])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(superposition,[],[f33,f211])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    k1_xboole_0 = sK1),
% 0.22/0.50    inference(global_subsumption,[],[f148,f166,f210])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f189])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f102,f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f152,f48])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f78,f147])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f144,f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(resolution,[],[f126,f75])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.22/0.50    inference(resolution,[],[f109,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f108,f71])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.22/0.50    inference(superposition,[],[f57,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f69,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    inference(resolution,[],[f36,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f68,f36])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(resolution,[],[f35,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.50    inference(resolution,[],[f143,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f32,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.22/0.50    inference(subsumption_resolution,[],[f142,f100])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f141])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f134,f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(resolution,[],[f130,f56])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f130,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~r1_tarski(sK2,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f75,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,k2_relat_1(sK3)) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f85,f100])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.22/0.50    inference(resolution,[],[f66,f71])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.22/0.50    inference(resolution,[],[f34,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.51  % (19409)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f153])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.22/0.51    inference(superposition,[],[f130,f147])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(superposition,[],[f65,f147])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f36,f211])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.51    inference(resolution,[],[f223,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.51    inference(equality_resolution,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f212,f221])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f35,f211])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.22/0.51    inference(backward_demodulation,[],[f214,f221])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.22/0.51    inference(backward_demodulation,[],[f70,f211])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 0.22/0.51    inference(resolution,[],[f289,f230])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 0.22/0.51    inference(forward_demodulation,[],[f222,f221])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.51    inference(backward_demodulation,[],[f65,f221])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f285,f287])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k1_relset_1(X0,sK2,sK3)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f281,f236])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(sK3) = k1_relset_1(X0,sK2,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f280,f56])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.22/0.51    inference(resolution,[],[f280,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (19411)------------------------------
% 0.22/0.51  % (19411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19411)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (19411)Memory used [KB]: 6268
% 0.22/0.51  % (19411)Time elapsed: 0.070 s
% 0.22/0.51  % (19411)------------------------------
% 0.22/0.51  % (19411)------------------------------
% 0.22/0.51  % (19403)Success in time 0.143 s
%------------------------------------------------------------------------------
