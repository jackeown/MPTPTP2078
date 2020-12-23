%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  250 (1280 expanded)
%              Number of leaves         :   34 ( 327 expanded)
%              Depth                    :   23
%              Number of atoms          :  822 (6355 expanded)
%              Number of equality atoms :  119 (1335 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f891,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f117,f127,f178,f282,f293,f319,f426,f483,f520,f567,f580,f718,f727,f757,f761,f780,f842,f890])).

fof(f890,plain,
    ( spl4_3
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f889])).

% (27878)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f889,plain,
    ( $false
    | spl4_3
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f884,f103])).

fof(f103,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f884,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f878,f883])).

fof(f883,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f879,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f44])).

fof(f44,plain,
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

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f879,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f222,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f222,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f878,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f877,f118])).

fof(f118,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f113,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f113,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f53])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f877,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f876,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f876,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f861,f54])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f861,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f378,f189])).

fof(f189,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f187,f53])).

fof(f187,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f77,f55])).

fof(f55,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f378,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f376])).

fof(f376,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f182,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f182,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f181,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f181,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f170,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f170,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0))))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f842,plain,
    ( spl4_11
    | spl4_12 ),
    inference(avatar_split_clause,[],[f841,f224,f221])).

fof(f224,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f841,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f52,f527])).

fof(f527,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f780,plain,
    ( spl4_2
    | ~ spl4_12
    | ~ spl4_18
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f779])).

fof(f779,plain,
    ( $false
    | spl4_2
    | ~ spl4_12
    | ~ spl4_18
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f778,f419])).

fof(f419,plain,
    ( ! [X0] : v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl4_18
  <=> ! [X0] : v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f778,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f777,f519])).

fof(f519,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl4_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f777,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f100,f225])).

fof(f225,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f224])).

fof(f100,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f761,plain,
    ( spl4_3
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f760])).

fof(f760,plain,
    ( $false
    | spl4_3
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f759,f736])).

fof(f736,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f735,f89])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f735,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f550,f225])).

fof(f550,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f549,f118])).

fof(f549,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f548,f51])).

fof(f548,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f537,f54])).

fof(f537,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f186,f189])).

fof(f186,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f185,f63])).

fof(f185,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f168,f64])).

fof(f168,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f65])).

fof(f759,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f758,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f758,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | spl4_3
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f103,f516])).

fof(f516,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl4_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f757,plain,
    ( spl4_2
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | spl4_2
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f755,f749])).

fof(f749,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f582,f516])).

fof(f582,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f100,f225])).

fof(f755,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f737,f753])).

fof(f753,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f751,f741])).

fof(f741,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f740,f88])).

fof(f740,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f193,f225])).

fof(f193,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(subsumption_resolution,[],[f192,f118])).

fof(f192,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f190,f51])).

fof(f190,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f62,f189])).

fof(f751,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(resolution,[],[f747,f206])).

fof(f206,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f201,f89])).

fof(f201,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(superposition,[],[f108,f76])).

fof(f108,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f94,f89])).

fof(f94,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f747,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f746,f516])).

fof(f746,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f52,f225])).

fof(f737,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f316,f225])).

fof(f316,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f315,f118])).

fof(f315,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f314,f51])).

fof(f314,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f313,f54])).

fof(f313,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f312,f66])).

fof(f312,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f311,f118])).

fof(f311,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f310,f51])).

fof(f310,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f305,f54])).

fof(f305,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f184,f189])).

fof(f184,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f183,f63])).

fof(f183,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f169,f64])).

fof(f169,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f61,f65])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f727,plain,
    ( ~ spl4_24
    | spl4_28
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f726,f280,f125,f507,f488])).

fof(f488,plain,
    ( spl4_24
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f507,plain,
    ( spl4_28
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f125,plain,
    ( spl4_5
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f280,plain,
    ( spl4_17
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f726,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f725,f88])).

fof(f725,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f724,f109])).

fof(f109,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f68,f88])).

fof(f724,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f628,f126])).

fof(f126,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f628,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_17 ),
    inference(superposition,[],[f378,f281])).

fof(f281,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f280])).

fof(f718,plain,
    ( ~ spl4_5
    | ~ spl4_12
    | spl4_20
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f717])).

fof(f717,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_12
    | spl4_20
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f716,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f716,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_12
    | spl4_20
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f715,f554])).

fof(f554,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f54,f519])).

fof(f715,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_12
    | spl4_20
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f714,f109])).

fof(f714,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_12
    | spl4_20
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f713,f126])).

fof(f713,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_12
    | spl4_20
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f711,f425])).

fof(f425,plain,
    ( ~ v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl4_20
  <=> v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f711,plain,
    ( v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(superposition,[],[f371,f590])).

fof(f590,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f588,f508])).

fof(f508,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f507])).

fof(f588,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(resolution,[],[f575,f206])).

fof(f575,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f563,f225])).

fof(f563,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),sK1,k2_relat_1(k2_funct_1(k1_xboole_0)))
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f312,f519])).

fof(f371,plain,(
    ! [X2] :
      ( v1_partfun1(k2_funct_1(X2),k1_relat_1(k2_funct_1(X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_xboole_0(k1_relat_1(k2_funct_1(X2))) ) ),
    inference(resolution,[],[f182,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f580,plain,
    ( spl4_3
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | spl4_3
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f578,f508])).

fof(f578,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f577,f89])).

fof(f577,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_3
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f556,f225])).

fof(f556,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f103,f519])).

fof(f567,plain,
    ( spl4_24
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl4_24
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f554,f489])).

fof(f489,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f488])).

fof(f520,plain,
    ( spl4_15
    | spl4_30
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f343,f224,f518,f270])).

fof(f343,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f342,f335])).

fof(f335,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f326,f88])).

fof(f326,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f193,f225])).

fof(f342,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | ~ spl4_12 ),
    inference(resolution,[],[f320,f106])).

fof(f106,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f92,f88])).

fof(f92,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f320,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f52,f225])).

fof(f483,plain,
    ( ~ spl4_5
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | ~ spl4_5
    | spl4_19 ),
    inference(subsumption_resolution,[],[f481,f109])).

fof(f481,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_5
    | spl4_19 ),
    inference(subsumption_resolution,[],[f480,f126])).

fof(f480,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl4_19 ),
    inference(resolution,[],[f422,f64])).

fof(f422,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl4_19
  <=> v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f426,plain,
    ( spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_5
    | ~ spl4_12
    | spl4_15 ),
    inference(avatar_split_clause,[],[f411,f270,f224,f125,f424,f421,f418])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0)
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0) )
    | ~ spl4_5
    | ~ spl4_12
    | spl4_15 ),
    inference(resolution,[],[f399,f211])).

fof(f211,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_partfun1(X3,k1_xboole_0)
      | ~ v1_funct_1(X3)
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(superposition,[],[f85,f89])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f399,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_12
    | spl4_15 ),
    inference(forward_demodulation,[],[f398,f89])).

fof(f398,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ spl4_5
    | ~ spl4_12
    | spl4_15 ),
    inference(subsumption_resolution,[],[f397,f109])).

fof(f397,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_12
    | spl4_15 ),
    inference(subsumption_resolution,[],[f396,f126])).

fof(f396,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_12
    | spl4_15 ),
    inference(subsumption_resolution,[],[f390,f346])).

fof(f346,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_12
    | spl4_15 ),
    inference(backward_demodulation,[],[f54,f344])).

fof(f344,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_12
    | spl4_15 ),
    inference(subsumption_resolution,[],[f343,f271])).

fof(f271,plain,
    ( k1_xboole_0 != sK0
    | spl4_15 ),
    inference(avatar_component_clause,[],[f270])).

fof(f390,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_12
    | spl4_15 ),
    inference(superposition,[],[f186,f351])).

fof(f351,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_12
    | spl4_15 ),
    inference(backward_demodulation,[],[f325,f344])).

fof(f325,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f189,f225])).

fof(f319,plain,
    ( spl4_2
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl4_2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f317,f100])).

fof(f317,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f316,f235])).

fof(f235,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f231,f53])).

fof(f231,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f222,f76])).

fof(f293,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f291,f57])).

fof(f291,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_16 ),
    inference(resolution,[],[f278,f158])).

fof(f158,plain,(
    ! [X0] :
      ( v1_partfun1(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f278,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl4_16
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f282,plain,
    ( ~ spl4_16
    | spl4_17
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f275,f125,f280,f277])).

fof(f275,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f274,f58])).

fof(f274,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(resolution,[],[f206,f213])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k1_xboole_0,X0,X1)
        | ~ v1_partfun1(k1_xboole_0,X0) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f208,f126])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | ~ v1_funct_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f85,f58])).

fof(f178,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f177])).

% (27875)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (27877)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (27867)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (27866)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (27869)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (27873)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (27871)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (27883)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f177,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f173,f86])).

fof(f86,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_1)).

fof(f173,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f123,f87])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_4
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f127,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f120,f125,f122])).

fof(f120,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f67,f58])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f117,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f115,f68])).

fof(f115,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f113,f112])).

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f111,f51])).

fof(f111,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f64,f97])).

fof(f97,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f104,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f56,f102,f99,f96])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (27876)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (27865)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (27879)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (27874)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (27868)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (27863)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (27865)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f891,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f104,f117,f127,f178,f282,f293,f319,f426,f483,f520,f567,f580,f718,f727,f757,f761,f780,f842,f890])).
% 0.20/0.50  fof(f890,plain,(
% 0.20/0.50    spl4_3 | ~spl4_11),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f889])).
% 0.20/0.50  % (27878)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  fof(f889,plain,(
% 0.20/0.50    $false | (spl4_3 | ~spl4_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f884,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f102])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl4_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f884,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_11),
% 0.20/0.50    inference(backward_demodulation,[],[f878,f883])).
% 0.20/0.50  fof(f883,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | ~spl4_11),
% 0.20/0.50    inference(subsumption_resolution,[],[f879,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f20])).
% 0.20/0.50  fof(f20,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.50  fof(f879,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 0.20/0.50    inference(superposition,[],[f222,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f221])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    spl4_11 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.50  fof(f878,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.20/0.50    inference(subsumption_resolution,[],[f877,f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f113,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.50    inference(resolution,[],[f59,f53])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f877,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f876,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f876,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f861,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f861,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f378,f189])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    sK1 = k2_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f187,f53])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(superposition,[],[f77,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f376])).
% 0.20/0.50  fof(f376,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(superposition,[],[f182,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f181,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0)))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f170,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0)))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(superposition,[],[f62,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.50  fof(f842,plain,(
% 0.20/0.50    spl4_11 | spl4_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f841,f224,f221])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    spl4_12 <=> k1_xboole_0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.50  fof(f841,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f52,f527])).
% 0.20/0.50  fof(f527,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f53,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f780,plain,(
% 0.20/0.50    spl4_2 | ~spl4_12 | ~spl4_18 | ~spl4_30),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f779])).
% 0.20/0.50  fof(f779,plain,(
% 0.20/0.50    $false | (spl4_2 | ~spl4_12 | ~spl4_18 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f778,f419])).
% 0.20/0.50  fof(f419,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)) ) | ~spl4_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f418])).
% 0.20/0.50  fof(f418,plain,(
% 0.20/0.50    spl4_18 <=> ! [X0] : v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.50  fof(f778,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_12 | ~spl4_30)),
% 0.20/0.50    inference(forward_demodulation,[],[f777,f519])).
% 0.20/0.50  fof(f519,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | ~spl4_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f518])).
% 0.20/0.50  fof(f518,plain,(
% 0.20/0.50    spl4_30 <=> k1_xboole_0 = sK2),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.50  fof(f777,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f100,f225])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl4_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f224])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f761,plain,(
% 0.20/0.50    spl4_3 | ~spl4_12 | ~spl4_15),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f760])).
% 0.20/0.50  fof(f760,plain,(
% 0.20/0.50    $false | (spl4_3 | ~spl4_12 | ~spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f759,f736])).
% 0.20/0.50  fof(f736,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl4_12),
% 0.20/0.50    inference(forward_demodulation,[],[f735,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f735,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2))))) | ~spl4_12),
% 0.20/0.50    inference(forward_demodulation,[],[f550,f225])).
% 0.20/0.50  fof(f550,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))),
% 0.20/0.50    inference(subsumption_resolution,[],[f549,f118])).
% 0.20/0.50  fof(f549,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f548,f51])).
% 0.20/0.50  fof(f548,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f537,f54])).
% 0.20/0.50  fof(f537,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f186,f189])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f185,f63])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f168,f64])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(superposition,[],[f62,f65])).
% 0.20/0.50  fof(f759,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_15)),
% 0.20/0.50    inference(forward_demodulation,[],[f758,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f47])).
% 0.20/0.50  fof(f758,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (spl4_3 | ~spl4_15)),
% 0.20/0.50    inference(forward_demodulation,[],[f103,f516])).
% 0.20/0.50  fof(f516,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | ~spl4_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f270])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    spl4_15 <=> k1_xboole_0 = sK0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.50  fof(f757,plain,(
% 0.20/0.50    spl4_2 | ~spl4_12 | ~spl4_15),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f756])).
% 0.20/0.50  fof(f756,plain,(
% 0.20/0.50    $false | (spl4_2 | ~spl4_12 | ~spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f755,f749])).
% 0.20/0.50  fof(f749,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_12 | ~spl4_15)),
% 0.20/0.50    inference(backward_demodulation,[],[f582,f516])).
% 0.20/0.50  fof(f582,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f100,f225])).
% 0.20/0.50  fof(f755,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl4_12 | ~spl4_15)),
% 0.20/0.50    inference(backward_demodulation,[],[f737,f753])).
% 0.20/0.50  fof(f753,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_12 | ~spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f751,f741])).
% 0.20/0.50  fof(f741,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_12),
% 0.20/0.50    inference(forward_demodulation,[],[f740,f88])).
% 0.20/0.50  fof(f740,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~spl4_12),
% 0.20/0.50    inference(forward_demodulation,[],[f193,f225])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f192,f118])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f190,f51])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f62,f189])).
% 0.20/0.50  fof(f751,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_12 | ~spl4_15)),
% 0.20/0.50    inference(resolution,[],[f747,f206])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~v1_funct_2(X3,k1_xboole_0,X2) | k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f205])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f201,f89])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 0.20/0.50    inference(superposition,[],[f108,f76])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f94,f89])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f747,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl4_12 | ~spl4_15)),
% 0.20/0.50    inference(backward_demodulation,[],[f746,f516])).
% 0.20/0.50  fof(f746,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl4_12),
% 0.20/0.50    inference(forward_demodulation,[],[f52,f225])).
% 0.20/0.50  fof(f737,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) | ~spl4_12),
% 0.20/0.50    inference(forward_demodulation,[],[f316,f225])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f315,f118])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f314,f51])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f313,f54])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f312,f66])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f311,f118])).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f310,f51])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f305,f54])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f184,f189])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f183,f63])).
% 0.20/0.50  fof(f183,plain,(
% 0.20/0.50    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f169,f64])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(superposition,[],[f61,f65])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f727,plain,(
% 0.20/0.50    ~spl4_24 | spl4_28 | ~spl4_5 | ~spl4_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f726,f280,f125,f507,f488])).
% 0.20/0.50  fof(f488,plain,(
% 0.20/0.50    spl4_24 <=> v2_funct_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.50  fof(f507,plain,(
% 0.20/0.50    spl4_28 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl4_5 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    spl4_17 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.50  fof(f726,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v2_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_17)),
% 0.20/0.50    inference(forward_demodulation,[],[f725,f88])).
% 0.20/0.50  fof(f725,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0))) | ~v2_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f724,f109])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    v1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(superposition,[],[f68,f88])).
% 0.20/0.50  fof(f724,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0))) | ~v2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_5 | ~spl4_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f628,f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    v1_funct_1(k1_xboole_0) | ~spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f125])).
% 0.20/0.50  fof(f628,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0))) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_17),
% 0.20/0.50    inference(superposition,[],[f378,f281])).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f280])).
% 0.20/0.50  fof(f718,plain,(
% 0.20/0.50    ~spl4_5 | ~spl4_12 | spl4_20 | ~spl4_28 | ~spl4_30),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f717])).
% 0.20/0.50  fof(f717,plain,(
% 0.20/0.50    $false | (~spl4_5 | ~spl4_12 | spl4_20 | ~spl4_28 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f716,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f716,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | ~spl4_12 | spl4_20 | ~spl4_28 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f715,f554])).
% 0.20/0.50  fof(f554,plain,(
% 0.20/0.50    v2_funct_1(k1_xboole_0) | ~spl4_30),
% 0.20/0.50    inference(backward_demodulation,[],[f54,f519])).
% 0.20/0.50  fof(f715,plain,(
% 0.20/0.50    ~v2_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | ~spl4_12 | spl4_20 | ~spl4_28 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f714,f109])).
% 0.20/0.50  fof(f714,plain,(
% 0.20/0.50    ~v1_relat_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | ~spl4_12 | spl4_20 | ~spl4_28 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f713,f126])).
% 0.20/0.50  fof(f713,plain,(
% 0.20/0.50    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl4_12 | spl4_20 | ~spl4_28 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f711,f425])).
% 0.20/0.50  fof(f425,plain,(
% 0.20/0.50    ~v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0) | spl4_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f424])).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    spl4_20 <=> v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.50  fof(f711,plain,(
% 0.20/0.50    v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl4_12 | ~spl4_28 | ~spl4_30)),
% 0.20/0.50    inference(superposition,[],[f371,f590])).
% 0.20/0.50  fof(f590,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_12 | ~spl4_28 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f588,f508])).
% 0.20/0.50  fof(f508,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f507])).
% 0.20/0.50  fof(f588,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_12 | ~spl4_30)),
% 0.20/0.50    inference(resolution,[],[f575,f206])).
% 0.20/0.50  fof(f575,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))) | (~spl4_12 | ~spl4_30)),
% 0.20/0.50    inference(forward_demodulation,[],[f563,f225])).
% 0.20/0.50  fof(f563,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(k1_xboole_0),sK1,k2_relat_1(k2_funct_1(k1_xboole_0))) | ~spl4_30),
% 0.20/0.50    inference(backward_demodulation,[],[f312,f519])).
% 0.20/0.50  fof(f371,plain,(
% 0.20/0.50    ( ! [X2] : (v1_partfun1(k2_funct_1(X2),k1_relat_1(k2_funct_1(X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v2_funct_1(X2) | ~v1_xboole_0(k1_relat_1(k2_funct_1(X2)))) )),
% 0.20/0.50    inference(resolution,[],[f182,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.20/0.50  fof(f580,plain,(
% 0.20/0.50    spl4_3 | ~spl4_12 | ~spl4_28 | ~spl4_30),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f579])).
% 0.20/0.50  fof(f579,plain,(
% 0.20/0.50    $false | (spl4_3 | ~spl4_12 | ~spl4_28 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f578,f508])).
% 0.20/0.50  fof(f578,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_12 | ~spl4_30)),
% 0.20/0.50    inference(forward_demodulation,[],[f577,f89])).
% 0.20/0.50  fof(f577,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_3 | ~spl4_12 | ~spl4_30)),
% 0.20/0.50    inference(forward_demodulation,[],[f556,f225])).
% 0.20/0.50  fof(f556,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl4_3 | ~spl4_30)),
% 0.20/0.50    inference(backward_demodulation,[],[f103,f519])).
% 0.20/0.50  fof(f567,plain,(
% 0.20/0.50    spl4_24 | ~spl4_30),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f566])).
% 0.20/0.50  fof(f566,plain,(
% 0.20/0.50    $false | (spl4_24 | ~spl4_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f554,f489])).
% 0.20/0.50  fof(f489,plain,(
% 0.20/0.50    ~v2_funct_1(k1_xboole_0) | spl4_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f488])).
% 0.20/0.50  fof(f520,plain,(
% 0.20/0.50    spl4_15 | spl4_30 | ~spl4_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f343,f224,f518,f270])).
% 0.20/0.50  fof(f343,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | ~spl4_12),
% 0.20/0.50    inference(subsumption_resolution,[],[f342,f335])).
% 0.20/0.50  fof(f335,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_12),
% 0.20/0.50    inference(forward_demodulation,[],[f326,f88])).
% 0.20/0.50  fof(f326,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~spl4_12),
% 0.20/0.50    inference(backward_demodulation,[],[f193,f225])).
% 0.20/0.50  fof(f342,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | ~spl4_12),
% 0.20/0.50    inference(resolution,[],[f320,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(forward_demodulation,[],[f92,f88])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f320,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl4_12),
% 0.20/0.50    inference(backward_demodulation,[],[f52,f225])).
% 0.20/0.50  fof(f483,plain,(
% 0.20/0.50    ~spl4_5 | spl4_19),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f482])).
% 0.20/0.50  fof(f482,plain,(
% 0.20/0.50    $false | (~spl4_5 | spl4_19)),
% 0.20/0.50    inference(subsumption_resolution,[],[f481,f109])).
% 0.20/0.50  fof(f481,plain,(
% 0.20/0.50    ~v1_relat_1(k1_xboole_0) | (~spl4_5 | spl4_19)),
% 0.20/0.50    inference(subsumption_resolution,[],[f480,f126])).
% 0.20/0.50  fof(f480,plain,(
% 0.20/0.50    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | spl4_19),
% 0.20/0.50    inference(resolution,[],[f422,f64])).
% 0.20/0.50  fof(f422,plain,(
% 0.20/0.50    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | spl4_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f421])).
% 0.20/0.50  fof(f421,plain,(
% 0.20/0.50    spl4_19 <=> v1_funct_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.50  fof(f426,plain,(
% 0.20/0.50    spl4_18 | ~spl4_19 | ~spl4_20 | ~spl4_5 | ~spl4_12 | spl4_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f411,f270,f224,f125,f424,f421,f418])).
% 0.20/0.50  fof(f411,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)) ) | (~spl4_5 | ~spl4_12 | spl4_15)),
% 0.20/0.50    inference(resolution,[],[f399,f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(X3,k1_xboole_0) | ~v1_funct_1(X3) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 0.20/0.50    inference(superposition,[],[f85,f89])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.20/0.50  fof(f399,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_5 | ~spl4_12 | spl4_15)),
% 0.20/0.50    inference(forward_demodulation,[],[f398,f89])).
% 0.20/0.50  fof(f398,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | (~spl4_5 | ~spl4_12 | spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f397,f109])).
% 0.20/0.50  fof(f397,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_relat_1(k1_xboole_0) | (~spl4_5 | ~spl4_12 | spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f396,f126])).
% 0.20/0.50  fof(f396,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_12 | spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f390,f346])).
% 0.20/0.50  fof(f346,plain,(
% 0.20/0.50    v2_funct_1(k1_xboole_0) | (~spl4_12 | spl4_15)),
% 0.20/0.50    inference(backward_demodulation,[],[f54,f344])).
% 0.20/0.50  fof(f344,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | (~spl4_12 | spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f343,f271])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    k1_xboole_0 != sK0 | spl4_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f270])).
% 0.20/0.50  fof(f390,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_12 | spl4_15)),
% 0.20/0.50    inference(superposition,[],[f186,f351])).
% 0.20/0.50  fof(f351,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl4_12 | spl4_15)),
% 0.20/0.50    inference(backward_demodulation,[],[f325,f344])).
% 0.20/0.50  fof(f325,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_12),
% 0.20/0.50    inference(backward_demodulation,[],[f189,f225])).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    spl4_2 | ~spl4_11),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f318])).
% 0.20/0.50  fof(f318,plain,(
% 0.20/0.50    $false | (spl4_2 | ~spl4_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f317,f100])).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl4_11),
% 0.20/0.50    inference(forward_demodulation,[],[f316,f235])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | ~spl4_11),
% 0.20/0.50    inference(subsumption_resolution,[],[f231,f53])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 0.20/0.50    inference(superposition,[],[f222,f76])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    spl4_16),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f292])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    $false | spl4_16),
% 0.20/0.50    inference(subsumption_resolution,[],[f291,f57])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | spl4_16),
% 0.20/0.50    inference(resolution,[],[f278,f158])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    ( ! [X0] : (v1_partfun1(k1_xboole_0,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(resolution,[],[f71,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl4_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f277])).
% 0.20/0.50  fof(f277,plain,(
% 0.20/0.50    spl4_16 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    ~spl4_16 | spl4_17 | ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f275,f125,f280,f277])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl4_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f274,f58])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f206,f213])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | ~v1_partfun1(k1_xboole_0,X0)) ) | ~spl4_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f208,f126])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f85,f58])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ~spl4_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f177])).
% 0.20/0.50  % (27875)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (27877)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (27867)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (27866)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (27869)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (27873)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (27871)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (27883)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    $false | ~spl4_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f173,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    v1_relat_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ? [X0] : (v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ? [X0] : (v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_1)).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    ~v1_relat_1(sK3) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f123,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    v1_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl4_4 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    spl4_4 | spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f120,f125,f122])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f67,f58])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl4_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    $false | spl4_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f68])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f113,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl4_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f51])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 0.20/0.51    inference(resolution,[],[f64,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ~v1_funct_1(k2_funct_1(sK2)) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl4_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f56,f102,f99,f96])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f45])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (27865)------------------------------
% 0.20/0.51  % (27865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27865)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (27865)Memory used [KB]: 11001
% 0.20/0.51  % (27865)Time elapsed: 0.083 s
% 0.20/0.51  % (27865)------------------------------
% 0.20/0.51  % (27865)------------------------------
% 0.20/0.51  % (27864)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (27870)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (27862)Success in time 0.16 s
%------------------------------------------------------------------------------
