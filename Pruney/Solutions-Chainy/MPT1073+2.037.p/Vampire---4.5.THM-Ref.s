%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 140 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  217 ( 402 expanded)
%              Number of equality atoms :   28 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f51,f62,f66,f71,f75,f84,f102,f120,f132,f170,f174])).

fof(f174,plain,
    ( ~ spl7_12
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f172,f131])).

fof(f131,plain,
    ( sK0 = k1_funct_1(sK3,sK6(sK3,sK0))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_12
  <=> sK0 = k1_funct_1(sK3,sK6(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f172,plain,
    ( sK0 != k1_funct_1(sK3,sK6(sK3,sK0))
    | ~ spl7_19 ),
    inference(resolution,[],[f169,f20])).

fof(f20,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | sK0 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f169,plain,
    ( m1_subset_1(sK6(sK3,sK0),sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_19
  <=> m1_subset_1(sK6(sK3,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f170,plain,
    ( spl7_19
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f138,f118,f69,f168])).

fof(f69,plain,
    ( spl7_6
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f118,plain,
    ( spl7_11
  <=> r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f138,plain,
    ( m1_subset_1(sK6(sK3,sK0),sK1)
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(resolution,[],[f124,f70])).

fof(f70,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK3,sK0),X0) )
    | ~ spl7_11 ),
    inference(resolution,[],[f119,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f119,plain,
    ( r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f132,plain,
    ( spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f110,f100,f130])).

fof(f100,plain,
    ( spl7_10
  <=> sP5(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f110,plain,
    ( sK0 = k1_funct_1(sK3,sK6(sK3,sK0))
    | ~ spl7_10 ),
    inference(resolution,[],[f101,f28])).

fof(f28,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | k1_funct_1(X0,sK6(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f101,plain,
    ( sP5(sK0,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f120,plain,
    ( spl7_11
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f109,f100,f118])).

fof(f109,plain,
    ( r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))
    | ~ spl7_10 ),
    inference(resolution,[],[f101,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | r2_hidden(sK6(X0,X2),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,
    ( spl7_10
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f88,f82,f60,f40,f100])).

fof(f40,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f60,plain,
    ( spl7_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f82,plain,
    ( spl7_9
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f88,plain,
    ( sP5(sK0,sK3)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f87,f61])).

fof(f61,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f87,plain,
    ( sP5(sK0,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f85,f41])).

fof(f41,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f85,plain,
    ( ~ v1_funct_1(sK3)
    | sP5(sK0,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f83,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl7_9
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f80,f73,f49,f82])).

fof(f49,plain,
    ( spl7_3
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f73,plain,
    ( spl7_7
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f80,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(superposition,[],[f50,f74])).

fof(f74,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f50,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f75,plain,
    ( spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f54,f45,f73])).

fof(f45,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f54,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f46,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f71,plain,
    ( spl7_6
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f67,f64,f45,f69])).

fof(f64,plain,
    ( spl7_5
  <=> m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f67,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f65,f55])).

fof(f55,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f46,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f65,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f53,f45,f64])).

fof(f53,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ spl7_2 ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f62,plain,
    ( spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f52,f45,f60])).

fof(f52,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f51,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8792)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (8783)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (8791)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (8784)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (8784)Refutation not found, incomplete strategy% (8784)------------------------------
% 0.22/0.49  % (8784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8784)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8784)Memory used [KB]: 10618
% 0.22/0.49  % (8784)Time elapsed: 0.069 s
% 0.22/0.49  % (8784)------------------------------
% 0.22/0.49  % (8784)------------------------------
% 0.22/0.49  % (8783)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f42,f47,f51,f62,f66,f71,f75,f84,f102,f120,f132,f170,f174])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ~spl7_12 | ~spl7_19),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    $false | (~spl7_12 | ~spl7_19)),
% 0.22/0.49    inference(subsumption_resolution,[],[f172,f131])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    sK0 = k1_funct_1(sK3,sK6(sK3,sK0)) | ~spl7_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl7_12 <=> sK0 = k1_funct_1(sK3,sK6(sK3,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK3,sK6(sK3,sK0)) | ~spl7_19),
% 0.22/0.49    inference(resolution,[],[f169,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.49  fof(f8,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.49    inference(negated_conjecture,[],[f7])).
% 0.22/0.49  fof(f7,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK3,sK0),sK1) | ~spl7_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f168])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    spl7_19 <=> m1_subset_1(sK6(sK3,sK0),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    spl7_19 | ~spl7_6 | ~spl7_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f138,f118,f69,f168])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl7_6 <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl7_11 <=> r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK3,sK0),sK1) | (~spl7_6 | ~spl7_11)),
% 0.22/0.49    inference(resolution,[],[f124,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl7_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) | m1_subset_1(sK6(sK3,sK0),X0)) ) | ~spl7_11),
% 0.22/0.49    inference(resolution,[],[f119,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) | ~spl7_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f118])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    spl7_12 | ~spl7_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f110,f100,f130])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl7_10 <=> sP5(sK0,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    sK0 = k1_funct_1(sK3,sK6(sK3,sK0)) | ~spl7_10),
% 0.22/0.49    inference(resolution,[],[f101,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~sP5(X2,X0) | k1_funct_1(X0,sK6(X0,X2)) = X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    sP5(sK0,sK3) | ~spl7_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl7_11 | ~spl7_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f109,f100,f118])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) | ~spl7_10),
% 0.22/0.49    inference(resolution,[],[f101,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~sP5(X2,X0) | r2_hidden(sK6(X0,X2),k1_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl7_10 | ~spl7_1 | ~spl7_4 | ~spl7_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f88,f82,f60,f40,f100])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl7_1 <=> v1_funct_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl7_4 <=> v1_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl7_9 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    sP5(sK0,sK3) | (~spl7_1 | ~spl7_4 | ~spl7_9)),
% 0.22/0.49    inference(subsumption_resolution,[],[f87,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    v1_relat_1(sK3) | ~spl7_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    sP5(sK0,sK3) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_9)),
% 0.22/0.49    inference(subsumption_resolution,[],[f85,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    v1_funct_1(sK3) | ~spl7_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f40])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ~v1_funct_1(sK3) | sP5(sK0,sK3) | ~v1_relat_1(sK3) | ~spl7_9),
% 0.22/0.49    inference(resolution,[],[f83,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP5(X2,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl7_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f82])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl7_9 | ~spl7_3 | ~spl7_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f80,f73,f49,f82])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl7_3 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl7_7 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    r2_hidden(sK0,k2_relat_1(sK3)) | (~spl7_3 | ~spl7_7)),
% 0.22/0.49    inference(superposition,[],[f50,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl7_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl7_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl7_7 | ~spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f54,f45,f73])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl7_2),
% 0.22/0.49    inference(resolution,[],[f46,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f45])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl7_6 | ~spl7_2 | ~spl7_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f67,f64,f45,f69])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl7_5 <=> m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | (~spl7_2 | ~spl7_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f65,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl7_2),
% 0.22/0.49    inference(resolution,[],[f46,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | ~spl7_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl7_5 | ~spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f53,f45,f64])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | ~spl7_2),
% 0.22/0.49    inference(resolution,[],[f46,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl7_4 | ~spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f45,f60])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    v1_relat_1(sK3) | ~spl7_2),
% 0.22/0.49    inference(resolution,[],[f46,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f49])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f45])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl7_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f40])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (8783)------------------------------
% 0.22/0.49  % (8783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8783)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (8783)Memory used [KB]: 6268
% 0.22/0.49  % (8783)Time elapsed: 0.064 s
% 0.22/0.49  % (8783)------------------------------
% 0.22/0.49  % (8783)------------------------------
% 0.22/0.49  % (8782)Success in time 0.13 s
%------------------------------------------------------------------------------
