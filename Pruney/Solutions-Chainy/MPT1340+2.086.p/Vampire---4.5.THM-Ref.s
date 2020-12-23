%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:31 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 854 expanded)
%              Number of leaves         :   34 ( 312 expanded)
%              Depth                    :   18
%              Number of atoms          :  771 (6197 expanded)
%              Number of equality atoms :  106 ( 805 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f239,f246,f266,f378,f439,f504,f612,f619,f680,f927,f1046,f1248,f1259,f1266])).

fof(f1266,plain,
    ( ~ spl5_52
    | spl5_53 ),
    inference(avatar_contradiction_clause,[],[f1265])).

fof(f1265,plain,
    ( $false
    | ~ spl5_52
    | spl5_53 ),
    inference(subsumption_resolution,[],[f1264,f129])).

fof(f129,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f125,f74])).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f125,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(resolution,[],[f65,f59])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
    & v2_funct_1(sK4)
    & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
      & v2_funct_1(sK4)
      & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1264,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl5_52
    | spl5_53 ),
    inference(subsumption_resolution,[],[f1261,f1242])).

fof(f1242,plain,
    ( v4_relat_1(sK4,k1_relat_1(sK4))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f1241])).

% (16856)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f1241,plain,
    ( spl5_52
  <=> v4_relat_1(sK4,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1261,plain,
    ( ~ v4_relat_1(sK4,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl5_53 ),
    inference(resolution,[],[f1247,f89])).

fof(f89,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f1247,plain,
    ( ~ v1_partfun1(sK4,k1_relat_1(sK4))
    | spl5_53 ),
    inference(avatar_component_clause,[],[f1245])).

fof(f1245,plain,
    ( spl5_53
  <=> v1_partfun1(sK4,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f1259,plain,
    ( ~ spl5_3
    | spl5_52 ),
    inference(avatar_contradiction_clause,[],[f1258])).

fof(f1258,plain,
    ( $false
    | ~ spl5_3
    | spl5_52 ),
    inference(subsumption_resolution,[],[f1253,f138])).

fof(f138,plain,(
    v4_relat_1(sK4,k2_struct_0(sK2)) ),
    inference(resolution,[],[f78,f105])).

fof(f105,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f97,f54])).

fof(f54,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK2) ),
    inference(superposition,[],[f59,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1253,plain,
    ( ~ v4_relat_1(sK4,k2_struct_0(sK2))
    | ~ spl5_3
    | spl5_52 ),
    inference(resolution,[],[f1251,f245])).

fof(f245,plain,
    ( v1_partfun1(sK4,k2_struct_0(sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl5_3
  <=> v1_partfun1(sK4,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1251,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK4,X0)
        | ~ v4_relat_1(sK4,X0) )
    | spl5_52 ),
    inference(subsumption_resolution,[],[f1250,f129])).

fof(f1250,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK4,X0)
        | ~ v1_partfun1(sK4,X0)
        | ~ v1_relat_1(sK4) )
    | spl5_52 ),
    inference(duplicate_literal_removal,[],[f1249])).

fof(f1249,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK4,X0)
        | ~ v1_partfun1(sK4,X0)
        | ~ v4_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4) )
    | spl5_52 ),
    inference(superposition,[],[f1243,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1243,plain,
    ( ~ v4_relat_1(sK4,k1_relat_1(sK4))
    | spl5_52 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1248,plain,
    ( ~ spl5_52
    | ~ spl5_53
    | ~ spl5_1
    | ~ spl5_28
    | spl5_29 ),
    inference(avatar_split_clause,[],[f1238,f597,f593,f232,f1245,f1241])).

fof(f232,plain,
    ( spl5_1
  <=> v1_partfun1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f593,plain,
    ( spl5_28
  <=> m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f597,plain,
    ( spl5_29
  <=> u1_struct_0(sK2) = k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f1238,plain,
    ( ~ v1_partfun1(sK4,k1_relat_1(sK4))
    | ~ v4_relat_1(sK4,k1_relat_1(sK4))
    | ~ spl5_1
    | ~ spl5_28
    | spl5_29 ),
    inference(equality_resolution,[],[f1157])).

fof(f1157,plain,
    ( ! [X21] :
        ( k1_relat_1(sK4) != X21
        | ~ v1_partfun1(sK4,X21)
        | ~ v4_relat_1(sK4,X21) )
    | ~ spl5_1
    | ~ spl5_28
    | spl5_29 ),
    inference(superposition,[],[f689,f1131])).

fof(f1131,plain,
    ( ! [X5] :
        ( u1_struct_0(sK2) = X5
        | ~ v1_partfun1(sK4,X5)
        | ~ v4_relat_1(sK4,X5) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f1130,f129])).

fof(f1130,plain,
    ( ! [X5] :
        ( u1_struct_0(sK2) = X5
        | ~ v1_relat_1(sK4)
        | ~ v1_partfun1(sK4,X5)
        | ~ v4_relat_1(sK4,X5) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f1121,f137])).

fof(f137,plain,(
    v4_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f78,f59])).

fof(f1121,plain,
    ( ! [X5] :
        ( u1_struct_0(sK2) = X5
        | ~ v4_relat_1(sK4,u1_struct_0(sK2))
        | ~ v1_relat_1(sK4)
        | ~ v1_partfun1(sK4,X5)
        | ~ v4_relat_1(sK4,X5) )
    | ~ spl5_1 ),
    inference(resolution,[],[f166,f234])).

fof(f234,plain,
    ( v1_partfun1(sK4,u1_struct_0(sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f232])).

fof(f166,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_partfun1(X2,X4)
      | X3 = X4
      | ~ v4_relat_1(X2,X4)
      | ~ v1_relat_1(X2)
      | ~ v1_partfun1(X2,X3)
      | ~ v4_relat_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X4,X2,X3] :
      ( X3 = X4
      | ~ v1_partfun1(X2,X4)
      | ~ v4_relat_1(X2,X4)
      | ~ v1_relat_1(X2)
      | ~ v1_partfun1(X2,X3)
      | ~ v4_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f75,f75])).

fof(f689,plain,
    ( u1_struct_0(sK2) != k1_relat_1(sK4)
    | ~ spl5_28
    | spl5_29 ),
    inference(subsumption_resolution,[],[f688,f129])).

fof(f688,plain,
    ( u1_struct_0(sK2) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_28
    | spl5_29 ),
    inference(subsumption_resolution,[],[f687,f57])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f687,plain,
    ( u1_struct_0(sK2) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_28
    | spl5_29 ),
    inference(subsumption_resolution,[],[f686,f61])).

fof(f61,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f686,plain,
    ( u1_struct_0(sK2) != k1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_28
    | spl5_29 ),
    inference(superposition,[],[f685,f73])).

fof(f73,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f685,plain,
    ( u1_struct_0(sK2) != k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_28
    | spl5_29 ),
    inference(subsumption_resolution,[],[f682,f594])).

fof(f594,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2))))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f593])).

fof(f682,plain,
    ( u1_struct_0(sK2) != k2_relat_1(k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2))))
    | spl5_29 ),
    inference(superposition,[],[f599,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f599,plain,
    ( u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f597])).

fof(f1046,plain,(
    spl5_31 ),
    inference(avatar_contradiction_clause,[],[f1045])).

fof(f1045,plain,
    ( $false
    | spl5_31 ),
    inference(subsumption_resolution,[],[f1044,f129])).

fof(f1044,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_31 ),
    inference(subsumption_resolution,[],[f1043,f57])).

fof(f1043,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_31 ),
    inference(subsumption_resolution,[],[f1042,f61])).

fof(f1042,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_31 ),
    inference(subsumption_resolution,[],[f1040,f220])).

fof(f220,plain,(
    r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),sK4,sK4) ),
    inference(forward_demodulation,[],[f219,f175])).

fof(f175,plain,(
    k2_struct_0(sK3) = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f167,f59])).

fof(f167,plain,
    ( k2_struct_0(sK3) = k2_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(superposition,[],[f77,f60])).

fof(f60,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f219,plain,(
    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) ),
    inference(subsumption_resolution,[],[f217,f56])).

fof(f56,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f217,plain,
    ( r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f211,f64])).

fof(f211,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4) ),
    inference(subsumption_resolution,[],[f210,f57])).

fof(f210,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f207,f58])).

fof(f58,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f207,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f92,f59])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f1040,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),sK4,sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_31 ),
    inference(superposition,[],[f607,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f607,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f605])).

fof(f605,plain,
    ( spl5_31
  <=> r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f927,plain,
    ( ~ spl5_28
    | ~ spl5_29
    | ~ spl5_31
    | ~ spl5_4
    | spl5_13
    | ~ spl5_27
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f926,f601,f589,f436,f356,f605,f597,f593])).

fof(f356,plain,
    ( spl5_4
  <=> sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f436,plain,
    ( spl5_13
  <=> r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_tops_2(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f589,plain,
    ( spl5_27
  <=> v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f601,plain,
    ( spl5_30
  <=> v2_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f926,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4)
    | u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2))))
    | ~ spl5_4
    | spl5_13
    | ~ spl5_27
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f925,f387])).

fof(f387,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl5_4 ),
    inference(resolution,[],[f358,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f44])).

% (16842)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f358,plain,
    ( sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f356])).

fof(f925,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4)
    | u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_13
    | ~ spl5_27
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f924,f590])).

fof(f590,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f589])).

fof(f924,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4)
    | u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_13
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f921,f602])).

fof(f602,plain,
    ( v2_funct_1(k2_funct_1(sK4))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f601])).

fof(f921,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_13 ),
    inference(superposition,[],[f438,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f438,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_tops_2(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f436])).

fof(f680,plain,(
    spl5_30 ),
    inference(avatar_contradiction_clause,[],[f679])).

fof(f679,plain,
    ( $false
    | spl5_30 ),
    inference(subsumption_resolution,[],[f678,f129])).

fof(f678,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_30 ),
    inference(subsumption_resolution,[],[f677,f57])).

fof(f677,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_30 ),
    inference(subsumption_resolution,[],[f676,f61])).

fof(f676,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_30 ),
    inference(resolution,[],[f675,f70])).

fof(f70,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f25,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f675,plain,
    ( ~ sP0(sK4)
    | spl5_30 ),
    inference(resolution,[],[f603,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f603,plain,
    ( ~ v2_funct_1(k2_funct_1(sK4))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f601])).

fof(f619,plain,
    ( ~ spl5_4
    | spl5_28 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | ~ spl5_4
    | spl5_28 ),
    inference(subsumption_resolution,[],[f616,f358])).

fof(f616,plain,
    ( ~ sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)
    | spl5_28 ),
    inference(resolution,[],[f595,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f595,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2))))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f593])).

fof(f612,plain,
    ( ~ spl5_4
    | spl5_27 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | ~ spl5_4
    | spl5_27 ),
    inference(subsumption_resolution,[],[f609,f358])).

fof(f609,plain,
    ( ~ sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)
    | spl5_27 ),
    inference(resolution,[],[f591,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f591,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f589])).

fof(f504,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f502,f56])).

fof(f502,plain,
    ( ~ l1_struct_0(sK3)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f501,f175])).

fof(f501,plain,
    ( k2_struct_0(sK3) != k2_relat_1(sK4)
    | ~ l1_struct_0(sK3)
    | spl5_5 ),
    inference(superposition,[],[f362,f64])).

fof(f362,plain,
    ( u1_struct_0(sK3) != k2_relat_1(sK4)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl5_5
  <=> u1_struct_0(sK3) = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f439,plain,
    ( ~ spl5_13
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f434,f360,f436])).

fof(f434,plain,
    ( u1_struct_0(sK3) != k2_relat_1(sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_tops_2(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    inference(inner_rewriting,[],[f433])).

fof(f433,plain,
    ( u1_struct_0(sK3) != k2_relat_1(sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    inference(forward_demodulation,[],[f432,f183])).

fof(f183,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
    inference(backward_demodulation,[],[f60,f175])).

fof(f432,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f431,f57])).

fof(f431,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f430,f58])).

fof(f430,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f429,f59])).

fof(f429,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f395,f61])).

fof(f395,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(sK4)
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f62,f84])).

fof(f62,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f378,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f377,f356])).

fof(f377,plain,(
    sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) ),
    inference(subsumption_resolution,[],[f376,f57])).

fof(f376,plain,
    ( sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f375,f188])).

fof(f188,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f110,f175])).

fof(f110,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f58,f64])).

fof(f375,plain,
    ( sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_relat_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f374,f61])).

fof(f374,plain,
    ( ~ v2_funct_1(sK4)
    | sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_relat_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f346,f186])).

fof(f186,plain,(
    k2_relat_1(sK4) = k2_relset_1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) ),
    inference(backward_demodulation,[],[f108,f175])).

fof(f108,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f100,f56])).

fof(f100,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f60,f64])).

fof(f346,plain,
    ( k2_relat_1(sK4) != k2_relset_1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)
    | ~ v2_funct_1(sK4)
    | sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_relat_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f83,f187])).

fof(f187,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_relat_1(sK4)))) ),
    inference(backward_demodulation,[],[f109,f175])).

fof(f109,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f101,f56])).

fof(f101,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f59,f64])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | sP1(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f35,f44])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f266,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f264,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f264,plain,
    ( v2_struct_0(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f263,f56])).

fof(f263,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f260,f63])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f260,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_2 ),
    inference(superposition,[],[f66,f238])).

fof(f238,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl5_2
  <=> k1_xboole_0 = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f246,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f241,f236,f243])).

fof(f241,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | v1_partfun1(sK4,k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f240,f57])).

fof(f240,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | v1_partfun1(sK4,k2_struct_0(sK2))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f227,f106])).

fof(f106,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f98,f54])).

fof(f98,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK2) ),
    inference(superposition,[],[f58,f64])).

fof(f227,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | v1_partfun1(sK4,k2_struct_0(sK2))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f93,f105])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f239,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f230,f236,f232])).

fof(f230,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | v1_partfun1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f229,f57])).

fof(f229,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | v1_partfun1(sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f226,f58])).

fof(f226,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | v1_partfun1(sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f93,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.49  % (16844)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.49  % (16843)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (16844)Refutation not found, incomplete strategy% (16844)------------------------------
% 0.23/0.52  % (16844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (16844)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (16844)Memory used [KB]: 6140
% 0.23/0.52  % (16844)Time elapsed: 0.097 s
% 0.23/0.52  % (16844)------------------------------
% 0.23/0.52  % (16844)------------------------------
% 0.23/0.52  % (16860)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.52  % (16847)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.53  % (16845)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (16845)Refutation not found, incomplete strategy% (16845)------------------------------
% 0.23/0.53  % (16845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (16845)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (16845)Memory used [KB]: 10746
% 0.23/0.53  % (16845)Time elapsed: 0.109 s
% 0.23/0.53  % (16845)------------------------------
% 0.23/0.53  % (16845)------------------------------
% 0.23/0.54  % (16861)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.54  % (16839)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.36/0.54  % (16853)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.36/0.54  % (16859)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.36/0.54  % (16862)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.36/0.55  % (16843)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f1268,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(avatar_sat_refutation,[],[f239,f246,f266,f378,f439,f504,f612,f619,f680,f927,f1046,f1248,f1259,f1266])).
% 1.36/0.55  fof(f1266,plain,(
% 1.36/0.55    ~spl5_52 | spl5_53),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f1265])).
% 1.36/0.55  fof(f1265,plain,(
% 1.36/0.55    $false | (~spl5_52 | spl5_53)),
% 1.36/0.55    inference(subsumption_resolution,[],[f1264,f129])).
% 1.36/0.55  fof(f129,plain,(
% 1.36/0.55    v1_relat_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f125,f74])).
% 1.36/0.55  fof(f74,plain,(
% 1.36/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.36/0.55  fof(f125,plain,(
% 1.36/0.55    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))),
% 1.36/0.55    inference(resolution,[],[f65,f59])).
% 1.36/0.55  fof(f59,plain,(
% 1.36/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f49,plain,(
% 1.36/0.55    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2)),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f48,f47,f46])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f47,plain,(
% 1.36/0.55    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f48,plain,(
% 1.36/0.55    ? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f19,plain,(
% 1.36/0.55    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.36/0.55    inference(flattening,[],[f18])).
% 1.36/0.55  fof(f18,plain,(
% 1.36/0.55    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f17])).
% 1.36/0.55  fof(f17,negated_conjecture,(
% 1.36/0.55    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.36/0.55    inference(negated_conjecture,[],[f16])).
% 1.36/0.55  fof(f16,conjecture,(
% 1.36/0.55    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 1.36/0.55  fof(f65,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f21])).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.36/0.55  fof(f1264,plain,(
% 1.36/0.55    ~v1_relat_1(sK4) | (~spl5_52 | spl5_53)),
% 1.36/0.55    inference(subsumption_resolution,[],[f1261,f1242])).
% 1.36/0.55  fof(f1242,plain,(
% 1.36/0.55    v4_relat_1(sK4,k1_relat_1(sK4)) | ~spl5_52),
% 1.36/0.55    inference(avatar_component_clause,[],[f1241])).
% 1.36/0.55  % (16856)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.36/0.55  fof(f1241,plain,(
% 1.36/0.55    spl5_52 <=> v4_relat_1(sK4,k1_relat_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 1.36/0.55  fof(f1261,plain,(
% 1.36/0.55    ~v4_relat_1(sK4,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl5_53),
% 1.36/0.55    inference(resolution,[],[f1247,f89])).
% 1.36/0.55  fof(f89,plain,(
% 1.36/0.55    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(equality_resolution,[],[f76])).
% 1.36/0.55  fof(f76,plain,(
% 1.36/0.55    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f51])).
% 1.36/0.55  fof(f51,plain,(
% 1.36/0.55    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(nnf_transformation,[],[f31])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(flattening,[],[f30])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.36/0.55  fof(f1247,plain,(
% 1.36/0.55    ~v1_partfun1(sK4,k1_relat_1(sK4)) | spl5_53),
% 1.36/0.55    inference(avatar_component_clause,[],[f1245])).
% 1.36/0.55  fof(f1245,plain,(
% 1.36/0.55    spl5_53 <=> v1_partfun1(sK4,k1_relat_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 1.36/0.55  fof(f1259,plain,(
% 1.36/0.55    ~spl5_3 | spl5_52),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f1258])).
% 1.36/0.55  fof(f1258,plain,(
% 1.36/0.55    $false | (~spl5_3 | spl5_52)),
% 1.36/0.55    inference(subsumption_resolution,[],[f1253,f138])).
% 1.36/0.55  fof(f138,plain,(
% 1.36/0.55    v4_relat_1(sK4,k2_struct_0(sK2))),
% 1.36/0.55    inference(resolution,[],[f78,f105])).
% 1.36/0.55  fof(f105,plain,(
% 1.36/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3))))),
% 1.36/0.55    inference(subsumption_resolution,[],[f97,f54])).
% 1.36/0.55  fof(f54,plain,(
% 1.36/0.55    l1_struct_0(sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f97,plain,(
% 1.36/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3)))) | ~l1_struct_0(sK2)),
% 1.36/0.55    inference(superposition,[],[f59,f64])).
% 1.36/0.55  fof(f64,plain,(
% 1.36/0.55    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,axiom,(
% 1.36/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.36/0.55  fof(f78,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f33])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.55  fof(f1253,plain,(
% 1.36/0.55    ~v4_relat_1(sK4,k2_struct_0(sK2)) | (~spl5_3 | spl5_52)),
% 1.36/0.55    inference(resolution,[],[f1251,f245])).
% 1.36/0.55  fof(f245,plain,(
% 1.36/0.55    v1_partfun1(sK4,k2_struct_0(sK2)) | ~spl5_3),
% 1.36/0.55    inference(avatar_component_clause,[],[f243])).
% 1.36/0.55  fof(f243,plain,(
% 1.36/0.55    spl5_3 <=> v1_partfun1(sK4,k2_struct_0(sK2))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.36/0.55  fof(f1251,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_partfun1(sK4,X0) | ~v4_relat_1(sK4,X0)) ) | spl5_52),
% 1.36/0.55    inference(subsumption_resolution,[],[f1250,f129])).
% 1.36/0.55  fof(f1250,plain,(
% 1.36/0.55    ( ! [X0] : (~v4_relat_1(sK4,X0) | ~v1_partfun1(sK4,X0) | ~v1_relat_1(sK4)) ) | spl5_52),
% 1.36/0.55    inference(duplicate_literal_removal,[],[f1249])).
% 1.36/0.55  fof(f1249,plain,(
% 1.36/0.55    ( ! [X0] : (~v4_relat_1(sK4,X0) | ~v1_partfun1(sK4,X0) | ~v4_relat_1(sK4,X0) | ~v1_relat_1(sK4)) ) | spl5_52),
% 1.36/0.55    inference(superposition,[],[f1243,f75])).
% 1.36/0.55  fof(f75,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f51])).
% 1.36/0.55  fof(f1243,plain,(
% 1.36/0.55    ~v4_relat_1(sK4,k1_relat_1(sK4)) | spl5_52),
% 1.36/0.55    inference(avatar_component_clause,[],[f1241])).
% 1.36/0.55  fof(f1248,plain,(
% 1.36/0.55    ~spl5_52 | ~spl5_53 | ~spl5_1 | ~spl5_28 | spl5_29),
% 1.36/0.55    inference(avatar_split_clause,[],[f1238,f597,f593,f232,f1245,f1241])).
% 1.36/0.55  fof(f232,plain,(
% 1.36/0.55    spl5_1 <=> v1_partfun1(sK4,u1_struct_0(sK2))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.36/0.55  fof(f593,plain,(
% 1.36/0.55    spl5_28 <=> m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2))))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.36/0.55  fof(f597,plain,(
% 1.36/0.55    spl5_29 <=> u1_struct_0(sK2) = k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.36/0.55  fof(f1238,plain,(
% 1.36/0.55    ~v1_partfun1(sK4,k1_relat_1(sK4)) | ~v4_relat_1(sK4,k1_relat_1(sK4)) | (~spl5_1 | ~spl5_28 | spl5_29)),
% 1.36/0.55    inference(equality_resolution,[],[f1157])).
% 1.36/0.55  fof(f1157,plain,(
% 1.36/0.55    ( ! [X21] : (k1_relat_1(sK4) != X21 | ~v1_partfun1(sK4,X21) | ~v4_relat_1(sK4,X21)) ) | (~spl5_1 | ~spl5_28 | spl5_29)),
% 1.36/0.55    inference(superposition,[],[f689,f1131])).
% 1.36/0.55  fof(f1131,plain,(
% 1.36/0.55    ( ! [X5] : (u1_struct_0(sK2) = X5 | ~v1_partfun1(sK4,X5) | ~v4_relat_1(sK4,X5)) ) | ~spl5_1),
% 1.36/0.55    inference(subsumption_resolution,[],[f1130,f129])).
% 1.36/0.55  fof(f1130,plain,(
% 1.36/0.55    ( ! [X5] : (u1_struct_0(sK2) = X5 | ~v1_relat_1(sK4) | ~v1_partfun1(sK4,X5) | ~v4_relat_1(sK4,X5)) ) | ~spl5_1),
% 1.36/0.55    inference(subsumption_resolution,[],[f1121,f137])).
% 1.36/0.55  fof(f137,plain,(
% 1.36/0.55    v4_relat_1(sK4,u1_struct_0(sK2))),
% 1.36/0.55    inference(resolution,[],[f78,f59])).
% 1.36/0.55  fof(f1121,plain,(
% 1.36/0.55    ( ! [X5] : (u1_struct_0(sK2) = X5 | ~v4_relat_1(sK4,u1_struct_0(sK2)) | ~v1_relat_1(sK4) | ~v1_partfun1(sK4,X5) | ~v4_relat_1(sK4,X5)) ) | ~spl5_1),
% 1.36/0.55    inference(resolution,[],[f166,f234])).
% 1.36/0.55  fof(f234,plain,(
% 1.36/0.55    v1_partfun1(sK4,u1_struct_0(sK2)) | ~spl5_1),
% 1.36/0.55    inference(avatar_component_clause,[],[f232])).
% 1.36/0.55  fof(f166,plain,(
% 1.36/0.55    ( ! [X4,X2,X3] : (~v1_partfun1(X2,X4) | X3 = X4 | ~v4_relat_1(X2,X4) | ~v1_relat_1(X2) | ~v1_partfun1(X2,X3) | ~v4_relat_1(X2,X3)) )),
% 1.36/0.55    inference(duplicate_literal_removal,[],[f162])).
% 1.36/0.55  fof(f162,plain,(
% 1.36/0.55    ( ! [X4,X2,X3] : (X3 = X4 | ~v1_partfun1(X2,X4) | ~v4_relat_1(X2,X4) | ~v1_relat_1(X2) | ~v1_partfun1(X2,X3) | ~v4_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 1.36/0.55    inference(superposition,[],[f75,f75])).
% 1.36/0.55  fof(f689,plain,(
% 1.36/0.55    u1_struct_0(sK2) != k1_relat_1(sK4) | (~spl5_28 | spl5_29)),
% 1.36/0.55    inference(subsumption_resolution,[],[f688,f129])).
% 1.36/0.55  fof(f688,plain,(
% 1.36/0.55    u1_struct_0(sK2) != k1_relat_1(sK4) | ~v1_relat_1(sK4) | (~spl5_28 | spl5_29)),
% 1.36/0.55    inference(subsumption_resolution,[],[f687,f57])).
% 1.36/0.55  fof(f57,plain,(
% 1.36/0.55    v1_funct_1(sK4)),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f687,plain,(
% 1.36/0.55    u1_struct_0(sK2) != k1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_28 | spl5_29)),
% 1.36/0.55    inference(subsumption_resolution,[],[f686,f61])).
% 1.36/0.55  fof(f61,plain,(
% 1.36/0.55    v2_funct_1(sK4)),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f686,plain,(
% 1.36/0.55    u1_struct_0(sK2) != k1_relat_1(sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_28 | spl5_29)),
% 1.36/0.55    inference(superposition,[],[f685,f73])).
% 1.36/0.55  fof(f73,plain,(
% 1.36/0.55    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f5])).
% 1.36/0.55  fof(f5,axiom,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.36/0.55  fof(f685,plain,(
% 1.36/0.55    u1_struct_0(sK2) != k2_relat_1(k2_funct_1(sK4)) | (~spl5_28 | spl5_29)),
% 1.36/0.55    inference(subsumption_resolution,[],[f682,f594])).
% 1.36/0.55  fof(f594,plain,(
% 1.36/0.55    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2)))) | ~spl5_28),
% 1.36/0.55    inference(avatar_component_clause,[],[f593])).
% 1.36/0.55  fof(f682,plain,(
% 1.36/0.55    u1_struct_0(sK2) != k2_relat_1(k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2)))) | spl5_29),
% 1.36/0.55    inference(superposition,[],[f599,f77])).
% 1.36/0.55  fof(f77,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f32])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.55  fof(f599,plain,(
% 1.36/0.55    u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)) | spl5_29),
% 1.36/0.55    inference(avatar_component_clause,[],[f597])).
% 1.36/0.55  fof(f1046,plain,(
% 1.36/0.55    spl5_31),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f1045])).
% 1.36/0.55  fof(f1045,plain,(
% 1.36/0.55    $false | spl5_31),
% 1.36/0.55    inference(subsumption_resolution,[],[f1044,f129])).
% 1.36/0.55  fof(f1044,plain,(
% 1.36/0.55    ~v1_relat_1(sK4) | spl5_31),
% 1.36/0.55    inference(subsumption_resolution,[],[f1043,f57])).
% 1.36/0.55  fof(f1043,plain,(
% 1.36/0.55    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_31),
% 1.36/0.55    inference(subsumption_resolution,[],[f1042,f61])).
% 1.36/0.55  fof(f1042,plain,(
% 1.36/0.55    ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_31),
% 1.36/0.55    inference(subsumption_resolution,[],[f1040,f220])).
% 1.36/0.55  fof(f220,plain,(
% 1.36/0.55    r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),sK4,sK4)),
% 1.36/0.55    inference(forward_demodulation,[],[f219,f175])).
% 1.36/0.55  fof(f175,plain,(
% 1.36/0.55    k2_struct_0(sK3) = k2_relat_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f167,f59])).
% 1.36/0.55  fof(f167,plain,(
% 1.36/0.55    k2_struct_0(sK3) = k2_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.36/0.55    inference(superposition,[],[f77,f60])).
% 1.36/0.55  fof(f60,plain,(
% 1.36/0.55    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f219,plain,(
% 1.36/0.55    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f217,f56])).
% 1.36/0.55  fof(f56,plain,(
% 1.36/0.55    l1_struct_0(sK3)),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f217,plain,(
% 1.36/0.55    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~l1_struct_0(sK3)),
% 1.36/0.55    inference(superposition,[],[f211,f64])).
% 1.36/0.55  fof(f211,plain,(
% 1.36/0.55    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f210,f57])).
% 1.36/0.55  fof(f210,plain,(
% 1.36/0.55    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4) | ~v1_funct_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f207,f58])).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f207,plain,(
% 1.36/0.55    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.36/0.55    inference(resolution,[],[f92,f59])).
% 1.36/0.55  fof(f92,plain,(
% 1.36/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.36/0.55    inference(duplicate_literal_removal,[],[f91])).
% 1.36/0.55  fof(f91,plain,(
% 1.36/0.55    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.36/0.55    inference(equality_resolution,[],[f88])).
% 1.36/0.55  fof(f88,plain,(
% 1.36/0.55    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f53])).
% 1.36/0.55  fof(f53,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.55    inference(nnf_transformation,[],[f41])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.55    inference(flattening,[],[f40])).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.55    inference(ennf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.36/0.55  fof(f1040,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),sK4,sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_31),
% 1.36/0.55    inference(superposition,[],[f607,f71])).
% 1.36/0.55  fof(f71,plain,(
% 1.36/0.55    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f26])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f6])).
% 1.36/0.55  fof(f6,axiom,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.36/0.55  fof(f607,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4) | spl5_31),
% 1.36/0.55    inference(avatar_component_clause,[],[f605])).
% 1.36/0.55  fof(f605,plain,(
% 1.36/0.55    spl5_31 <=> r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.36/0.55  fof(f927,plain,(
% 1.36/0.55    ~spl5_28 | ~spl5_29 | ~spl5_31 | ~spl5_4 | spl5_13 | ~spl5_27 | ~spl5_30),
% 1.36/0.55    inference(avatar_split_clause,[],[f926,f601,f589,f436,f356,f605,f597,f593])).
% 1.36/0.55  fof(f356,plain,(
% 1.36/0.55    spl5_4 <=> sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.36/0.55  fof(f436,plain,(
% 1.36/0.55    spl5_13 <=> r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_tops_2(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.36/0.55  fof(f589,plain,(
% 1.36/0.55    spl5_27 <=> v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.36/0.55  fof(f601,plain,(
% 1.36/0.55    spl5_30 <=> v2_funct_1(k2_funct_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.36/0.55  fof(f926,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4) | u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2)))) | (~spl5_4 | spl5_13 | ~spl5_27 | ~spl5_30)),
% 1.36/0.55    inference(subsumption_resolution,[],[f925,f387])).
% 1.36/0.55  fof(f387,plain,(
% 1.36/0.55    v1_funct_1(k2_funct_1(sK4)) | ~spl5_4),
% 1.36/0.55    inference(resolution,[],[f358,f80])).
% 1.36/0.55  fof(f80,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | v1_funct_1(k2_funct_1(X2))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f52])).
% 1.36/0.55  fof(f52,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP1(X0,X1,X2))),
% 1.36/0.55    inference(nnf_transformation,[],[f44])).
% 1.36/0.55  % (16842)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP1(X0,X1,X2))),
% 1.36/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.36/0.55  fof(f358,plain,(
% 1.36/0.55    sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) | ~spl5_4),
% 1.36/0.55    inference(avatar_component_clause,[],[f356])).
% 1.36/0.55  fof(f925,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4) | u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2)))) | ~v1_funct_1(k2_funct_1(sK4)) | (spl5_13 | ~spl5_27 | ~spl5_30)),
% 1.36/0.55    inference(subsumption_resolution,[],[f924,f590])).
% 1.36/0.55  fof(f590,plain,(
% 1.36/0.55    v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2)) | ~spl5_27),
% 1.36/0.55    inference(avatar_component_clause,[],[f589])).
% 1.36/0.55  fof(f924,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4) | u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4)) | (spl5_13 | ~spl5_30)),
% 1.36/0.55    inference(subsumption_resolution,[],[f921,f602])).
% 1.36/0.55  fof(f602,plain,(
% 1.36/0.55    v2_funct_1(k2_funct_1(sK4)) | ~spl5_30),
% 1.36/0.55    inference(avatar_component_clause,[],[f601])).
% 1.36/0.55  fof(f921,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_funct_1(k2_funct_1(sK4)),sK4) | ~v2_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK2) != k2_relset_1(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4)) | spl5_13),
% 1.36/0.55    inference(superposition,[],[f438,f84])).
% 1.36/0.55  fof(f84,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.55    inference(flattening,[],[f36])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.55    inference(ennf_transformation,[],[f15])).
% 1.36/0.55  fof(f15,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.36/0.55  fof(f438,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_tops_2(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | spl5_13),
% 1.36/0.55    inference(avatar_component_clause,[],[f436])).
% 1.36/0.55  fof(f680,plain,(
% 1.36/0.55    spl5_30),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f679])).
% 1.36/0.55  fof(f679,plain,(
% 1.36/0.55    $false | spl5_30),
% 1.36/0.55    inference(subsumption_resolution,[],[f678,f129])).
% 1.36/0.55  fof(f678,plain,(
% 1.36/0.55    ~v1_relat_1(sK4) | spl5_30),
% 1.36/0.55    inference(subsumption_resolution,[],[f677,f57])).
% 1.36/0.55  fof(f677,plain,(
% 1.36/0.55    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_30),
% 1.36/0.55    inference(subsumption_resolution,[],[f676,f61])).
% 1.36/0.55  fof(f676,plain,(
% 1.36/0.55    ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_30),
% 1.36/0.55    inference(resolution,[],[f675,f70])).
% 1.36/0.55  fof(f70,plain,(
% 1.36/0.55    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f43])).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(definition_folding,[],[f25,f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 1.36/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f24])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.36/0.55  fof(f675,plain,(
% 1.36/0.55    ~sP0(sK4) | spl5_30),
% 1.36/0.55    inference(resolution,[],[f603,f69])).
% 1.36/0.55  fof(f69,plain,(
% 1.36/0.55    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f50])).
% 1.36/0.55  fof(f50,plain,(
% 1.36/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 1.36/0.55    inference(nnf_transformation,[],[f42])).
% 1.36/0.55  fof(f603,plain,(
% 1.36/0.55    ~v2_funct_1(k2_funct_1(sK4)) | spl5_30),
% 1.36/0.55    inference(avatar_component_clause,[],[f601])).
% 1.36/0.55  fof(f619,plain,(
% 1.36/0.55    ~spl5_4 | spl5_28),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f618])).
% 1.36/0.55  fof(f618,plain,(
% 1.36/0.55    $false | (~spl5_4 | spl5_28)),
% 1.36/0.55    inference(subsumption_resolution,[],[f616,f358])).
% 1.36/0.55  fof(f616,plain,(
% 1.36/0.55    ~sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) | spl5_28),
% 1.36/0.55    inference(resolution,[],[f595,f82])).
% 1.36/0.55  fof(f82,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP1(X0,X1,X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f52])).
% 1.36/0.55  fof(f595,plain,(
% 1.36/0.55    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),u1_struct_0(sK2)))) | spl5_28),
% 1.36/0.55    inference(avatar_component_clause,[],[f593])).
% 1.36/0.55  fof(f612,plain,(
% 1.36/0.55    ~spl5_4 | spl5_27),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f611])).
% 1.36/0.55  fof(f611,plain,(
% 1.36/0.55    $false | (~spl5_4 | spl5_27)),
% 1.36/0.55    inference(subsumption_resolution,[],[f609,f358])).
% 1.36/0.55  fof(f609,plain,(
% 1.36/0.55    ~sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) | spl5_27),
% 1.36/0.55    inference(resolution,[],[f591,f81])).
% 1.36/0.55  fof(f81,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f52])).
% 1.36/0.55  fof(f591,plain,(
% 1.36/0.55    ~v1_funct_2(k2_funct_1(sK4),k2_relat_1(sK4),u1_struct_0(sK2)) | spl5_27),
% 1.36/0.55    inference(avatar_component_clause,[],[f589])).
% 1.36/0.55  fof(f504,plain,(
% 1.36/0.55    spl5_5),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f503])).
% 1.36/0.55  fof(f503,plain,(
% 1.36/0.55    $false | spl5_5),
% 1.36/0.55    inference(subsumption_resolution,[],[f502,f56])).
% 1.36/0.55  fof(f502,plain,(
% 1.36/0.55    ~l1_struct_0(sK3) | spl5_5),
% 1.36/0.55    inference(subsumption_resolution,[],[f501,f175])).
% 1.36/0.55  fof(f501,plain,(
% 1.36/0.55    k2_struct_0(sK3) != k2_relat_1(sK4) | ~l1_struct_0(sK3) | spl5_5),
% 1.36/0.55    inference(superposition,[],[f362,f64])).
% 1.36/0.55  fof(f362,plain,(
% 1.36/0.55    u1_struct_0(sK3) != k2_relat_1(sK4) | spl5_5),
% 1.36/0.55    inference(avatar_component_clause,[],[f360])).
% 1.36/0.55  fof(f360,plain,(
% 1.36/0.55    spl5_5 <=> u1_struct_0(sK3) = k2_relat_1(sK4)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.36/0.55  fof(f439,plain,(
% 1.36/0.55    ~spl5_13 | ~spl5_5),
% 1.36/0.55    inference(avatar_split_clause,[],[f434,f360,f436])).
% 1.36/0.55  fof(f434,plain,(
% 1.36/0.55    u1_struct_0(sK3) != k2_relat_1(sK4) | ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK4),k2_tops_2(k2_relat_1(sK4),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 1.36/0.55    inference(inner_rewriting,[],[f433])).
% 1.36/0.55  fof(f433,plain,(
% 1.36/0.55    u1_struct_0(sK3) != k2_relat_1(sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 1.36/0.55    inference(forward_demodulation,[],[f432,f183])).
% 1.36/0.55  fof(f183,plain,(
% 1.36/0.55    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_relat_1(sK4)),
% 1.36/0.55    inference(backward_demodulation,[],[f60,f175])).
% 1.36/0.55  fof(f432,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f431,f57])).
% 1.36/0.55  fof(f431,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f430,f58])).
% 1.36/0.55  fof(f430,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f429,f59])).
% 1.36/0.55  fof(f429,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f395,f61])).
% 1.36/0.55  fof(f395,plain,(
% 1.36/0.55    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~v2_funct_1(sK4) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.36/0.55    inference(superposition,[],[f62,f84])).
% 1.36/0.56  fof(f62,plain,(
% 1.36/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)),
% 1.36/0.56    inference(cnf_transformation,[],[f49])).
% 1.36/0.56  fof(f378,plain,(
% 1.36/0.56    spl5_4),
% 1.36/0.56    inference(avatar_split_clause,[],[f377,f356])).
% 1.36/0.56  fof(f377,plain,(
% 1.36/0.56    sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)),
% 1.36/0.56    inference(subsumption_resolution,[],[f376,f57])).
% 1.36/0.56  fof(f376,plain,(
% 1.36/0.56    sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) | ~v1_funct_1(sK4)),
% 1.36/0.56    inference(subsumption_resolution,[],[f375,f188])).
% 1.36/0.56  fof(f188,plain,(
% 1.36/0.56    v1_funct_2(sK4,u1_struct_0(sK2),k2_relat_1(sK4))),
% 1.36/0.56    inference(backward_demodulation,[],[f110,f175])).
% 1.36/0.56  fof(f110,plain,(
% 1.36/0.56    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))),
% 1.36/0.56    inference(subsumption_resolution,[],[f102,f56])).
% 1.36/0.56  fof(f102,plain,(
% 1.36/0.56    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~l1_struct_0(sK3)),
% 1.36/0.56    inference(superposition,[],[f58,f64])).
% 1.36/0.56  fof(f375,plain,(
% 1.36/0.56    sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_relat_1(sK4)) | ~v1_funct_1(sK4)),
% 1.36/0.56    inference(subsumption_resolution,[],[f374,f61])).
% 1.36/0.56  fof(f374,plain,(
% 1.36/0.56    ~v2_funct_1(sK4) | sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_relat_1(sK4)) | ~v1_funct_1(sK4)),
% 1.36/0.56    inference(subsumption_resolution,[],[f346,f186])).
% 1.36/0.56  fof(f186,plain,(
% 1.36/0.56    k2_relat_1(sK4) = k2_relset_1(u1_struct_0(sK2),k2_relat_1(sK4),sK4)),
% 1.36/0.56    inference(backward_demodulation,[],[f108,f175])).
% 1.36/0.56  fof(f108,plain,(
% 1.36/0.56    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 1.36/0.56    inference(subsumption_resolution,[],[f100,f56])).
% 1.36/0.56  fof(f100,plain,(
% 1.36/0.56    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~l1_struct_0(sK3)),
% 1.36/0.56    inference(superposition,[],[f60,f64])).
% 1.36/0.56  fof(f346,plain,(
% 1.36/0.56    k2_relat_1(sK4) != k2_relset_1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) | ~v2_funct_1(sK4) | sP1(u1_struct_0(sK2),k2_relat_1(sK4),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_relat_1(sK4)) | ~v1_funct_1(sK4)),
% 1.36/0.56    inference(resolution,[],[f83,f187])).
% 1.36/0.56  fof(f187,plain,(
% 1.36/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_relat_1(sK4))))),
% 1.36/0.56    inference(backward_demodulation,[],[f109,f175])).
% 1.36/0.56  fof(f109,plain,(
% 1.36/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))),
% 1.36/0.56    inference(subsumption_resolution,[],[f101,f56])).
% 1.36/0.56  fof(f101,plain,(
% 1.36/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~l1_struct_0(sK3)),
% 1.36/0.56    inference(superposition,[],[f59,f64])).
% 1.36/0.56  fof(f83,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | sP1(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f45])).
% 1.36/0.56  fof(f45,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (sP1(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.56    inference(definition_folding,[],[f35,f44])).
% 1.36/0.56  fof(f35,plain,(
% 1.36/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.56    inference(flattening,[],[f34])).
% 1.36/0.56  fof(f34,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.56    inference(ennf_transformation,[],[f12])).
% 1.36/0.56  fof(f12,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.36/0.56  fof(f266,plain,(
% 1.36/0.56    ~spl5_2),
% 1.36/0.56    inference(avatar_contradiction_clause,[],[f265])).
% 1.36/0.56  fof(f265,plain,(
% 1.36/0.56    $false | ~spl5_2),
% 1.36/0.56    inference(subsumption_resolution,[],[f264,f55])).
% 1.36/0.56  fof(f55,plain,(
% 1.36/0.56    ~v2_struct_0(sK3)),
% 1.36/0.56    inference(cnf_transformation,[],[f49])).
% 1.36/0.56  fof(f264,plain,(
% 1.36/0.56    v2_struct_0(sK3) | ~spl5_2),
% 1.36/0.56    inference(subsumption_resolution,[],[f263,f56])).
% 1.36/0.56  fof(f263,plain,(
% 1.36/0.56    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl5_2),
% 1.36/0.56    inference(subsumption_resolution,[],[f260,f63])).
% 1.36/0.56  fof(f63,plain,(
% 1.36/0.56    v1_xboole_0(k1_xboole_0)),
% 1.36/0.56    inference(cnf_transformation,[],[f1])).
% 1.36/0.56  fof(f1,axiom,(
% 1.36/0.56    v1_xboole_0(k1_xboole_0)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.36/0.56  fof(f260,plain,(
% 1.36/0.56    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl5_2),
% 1.36/0.56    inference(superposition,[],[f66,f238])).
% 1.36/0.56  fof(f238,plain,(
% 1.36/0.56    k1_xboole_0 = u1_struct_0(sK3) | ~spl5_2),
% 1.36/0.56    inference(avatar_component_clause,[],[f236])).
% 1.36/0.56  fof(f236,plain,(
% 1.36/0.56    spl5_2 <=> k1_xboole_0 = u1_struct_0(sK3)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.36/0.56  fof(f66,plain,(
% 1.36/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f23])).
% 1.36/0.56  fof(f23,plain,(
% 1.36/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.36/0.56    inference(flattening,[],[f22])).
% 1.36/0.56  fof(f22,plain,(
% 1.36/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f14])).
% 1.36/0.56  fof(f14,axiom,(
% 1.36/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.36/0.56  fof(f246,plain,(
% 1.36/0.56    spl5_3 | spl5_2),
% 1.36/0.56    inference(avatar_split_clause,[],[f241,f236,f243])).
% 1.36/0.56  fof(f241,plain,(
% 1.36/0.56    k1_xboole_0 = u1_struct_0(sK3) | v1_partfun1(sK4,k2_struct_0(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f240,f57])).
% 1.36/0.56  fof(f240,plain,(
% 1.36/0.56    k1_xboole_0 = u1_struct_0(sK3) | v1_partfun1(sK4,k2_struct_0(sK2)) | ~v1_funct_1(sK4)),
% 1.36/0.56    inference(subsumption_resolution,[],[f227,f106])).
% 1.36/0.56  fof(f106,plain,(
% 1.36/0.56    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3))),
% 1.36/0.56    inference(subsumption_resolution,[],[f98,f54])).
% 1.36/0.56  fof(f98,plain,(
% 1.36/0.56    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3)) | ~l1_struct_0(sK2)),
% 1.36/0.56    inference(superposition,[],[f58,f64])).
% 1.36/0.56  fof(f227,plain,(
% 1.36/0.56    k1_xboole_0 = u1_struct_0(sK3) | v1_partfun1(sK4,k2_struct_0(sK2)) | ~v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.36/0.56    inference(resolution,[],[f93,f105])).
% 1.36/0.56  fof(f93,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.56    inference(duplicate_literal_removal,[],[f85])).
% 1.36/0.56  fof(f85,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f39])).
% 1.36/0.56  fof(f39,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.36/0.56    inference(flattening,[],[f38])).
% 1.36/0.56  fof(f38,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.36/0.56    inference(ennf_transformation,[],[f11])).
% 1.36/0.56  fof(f11,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 1.36/0.56  fof(f239,plain,(
% 1.36/0.56    spl5_1 | spl5_2),
% 1.36/0.56    inference(avatar_split_clause,[],[f230,f236,f232])).
% 1.36/0.56  fof(f230,plain,(
% 1.36/0.56    k1_xboole_0 = u1_struct_0(sK3) | v1_partfun1(sK4,u1_struct_0(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f229,f57])).
% 1.36/0.56  fof(f229,plain,(
% 1.36/0.56    k1_xboole_0 = u1_struct_0(sK3) | v1_partfun1(sK4,u1_struct_0(sK2)) | ~v1_funct_1(sK4)),
% 1.36/0.56    inference(subsumption_resolution,[],[f226,f58])).
% 1.36/0.56  fof(f226,plain,(
% 1.36/0.56    k1_xboole_0 = u1_struct_0(sK3) | v1_partfun1(sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.36/0.56    inference(resolution,[],[f93,f59])).
% 1.36/0.56  % SZS output end Proof for theBenchmark
% 1.36/0.56  % (16843)------------------------------
% 1.36/0.56  % (16843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (16843)Termination reason: Refutation
% 1.36/0.56  
% 1.36/0.56  % (16843)Memory used [KB]: 6652
% 1.36/0.56  % (16843)Time elapsed: 0.130 s
% 1.36/0.56  % (16843)------------------------------
% 1.36/0.56  % (16843)------------------------------
% 1.36/0.56  % (16857)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.36/0.56  % (16838)Success in time 0.194 s
%------------------------------------------------------------------------------
