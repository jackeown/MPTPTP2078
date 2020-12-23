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
% DateTime   : Thu Dec  3 13:02:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 890 expanded)
%              Number of leaves         :   22 ( 280 expanded)
%              Depth                    :   29
%              Number of atoms          :  696 (8821 expanded)
%              Number of equality atoms :  205 (3066 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f746,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f178,f334,f366,f707,f745])).

fof(f745,plain,
    ( ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f743,f156])).

fof(f156,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f125,f59])).

fof(f59,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f49,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

% (4145)Refutation not found, incomplete strategy% (4145)------------------------------
% (4145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4145)Termination reason: Refutation not found, incomplete strategy

% (4145)Memory used [KB]: 10746
% (4145)Time elapsed: 0.159 s
% (4145)------------------------------
% (4145)------------------------------
fof(f125,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f55,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f743,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f742,f53])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f742,plain,
    ( ~ v1_funct_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f741,f168])).

fof(f168,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f741,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f740,f100])).

fof(f100,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f84,f88])).

% (4157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f88,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f740,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f365,f247])).

% (4154)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f247,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f244,f246])).

fof(f246,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f245,f102])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f94,f88])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f245,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f233,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f233,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f60,f208])).

fof(f208,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f205,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f205,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f128,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

% (4148)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f126,f53])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f55,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f244,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f243,f53])).

fof(f243,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f242,f55])).

fof(f242,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f241,f56])).

% (4149)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f241,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f236,f58])).

fof(f236,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f90,f208])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f365,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(k5_relat_1(X1,sK3))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X1) != sK1 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl4_8
  <=> ! [X1] :
        ( k2_relat_1(X1) != sK1
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f707,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f705,f325])).

fof(f325,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f705,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f704,f56])).

% (4140)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f704,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f703,f64])).

fof(f64,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f703,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f702,f164])).

fof(f164,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f131,f148])).

fof(f148,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f147,f56])).

fof(f147,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f146,f57])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f146,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f145,f58])).

fof(f145,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f144,f53])).

fof(f144,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f143,f54])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f143,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f141,f55])).

fof(f141,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f60,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f131,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f58,f92])).

fof(f702,plain,
    ( sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f701])).

fof(f701,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(superposition,[],[f436,f684])).

fof(f684,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f379,f681])).

fof(f681,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f680,f168])).

fof(f680,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f679,f53])).

fof(f679,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f678,f156])).

fof(f678,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f676])).

fof(f676,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != k2_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(superposition,[],[f670,f247])).

fof(f670,plain,
    ( ! [X2] :
        ( k6_partfun1(sK0) != k5_relat_1(X2,sK3)
        | k2_relat_1(X2) != sK1
        | k2_funct_1(sK3) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f669,f164])).

fof(f669,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != sK1
        | k5_relat_1(X2,sK3) != k6_partfun1(k2_relat_1(sK3))
        | k2_funct_1(sK3) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f668,f325])).

fof(f668,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != sK1
        | k5_relat_1(X2,sK3) != k6_partfun1(k2_relat_1(sK3))
        | k2_funct_1(sK3) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f163,f344])).

fof(f344,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl4_5
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f163,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK1
      | k5_relat_1(X2,sK3) != k6_partfun1(k2_relat_1(sK3))
      | k2_funct_1(sK3) = X2
      | ~ v2_funct_1(sK3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f160,f56])).

fof(f160,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK1
      | k5_relat_1(X2,sK3) != k6_partfun1(k2_relat_1(sK3))
      | k2_funct_1(sK3) = X2
      | ~ v2_funct_1(sK3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f97,f157])).

fof(f157,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f130,f123])).

fof(f123,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(global_subsumption,[],[f58,f122])).

fof(f122,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f121,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f121,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f57,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f130,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f58,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f88])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f379,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f378,f157])).

fof(f378,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f377,f325])).

fof(f377,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f369,f56])).

fof(f369,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f344,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f88])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f436,plain,
    ( ! [X2] :
        ( k5_relat_1(X2,sK2) != k6_partfun1(sK1)
        | k2_relat_1(X2) != sK0
        | k2_funct_1(sK2) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f435,f156])).

fof(f435,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != sK0
        | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2)
        | k2_funct_1(sK2) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f155,f168])).

fof(f155,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK0
      | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2)
      | k2_funct_1(sK2) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f154,f53])).

fof(f154,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK0
      | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2)
      | k2_funct_1(sK2) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f152,f61])).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f152,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK0
      | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2)
      | k2_funct_1(sK2) = X2
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f97,f149])).

fof(f149,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f124,f120])).

fof(f120,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f55,f119])).

fof(f119,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f118,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f54,f75])).

fof(f124,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f55,f96])).

fof(f366,plain,
    ( spl4_5
    | spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f359,f324,f364,f342])).

fof(f359,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != sK1
        | v2_funct_1(sK3)
        | ~ v2_funct_1(k5_relat_1(X1,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f162,f325])).

fof(f162,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK1
      | v2_funct_1(sK3)
      | ~ v2_funct_1(k5_relat_1(X1,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f159,f56])).

fof(f159,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK1
      | v2_funct_1(sK3)
      | ~ v2_funct_1(k5_relat_1(X1,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f82,f157])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f334,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f332,f95])).

fof(f95,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f332,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_3 ),
    inference(resolution,[],[f331,f58])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_3 ),
    inference(resolution,[],[f326,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f326,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f324])).

fof(f178,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f176,f95])).

fof(f176,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f175,f55])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f169,f93])).

fof(f169,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (4151)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (4135)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (4131)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (4144)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (4137)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (4153)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (4130)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (4142)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (4139)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (4143)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (4132)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (4158)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (4155)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (4134)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (4150)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (4147)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (4138)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (4145)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (4129)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (4156)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (4153)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (4136)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (4141)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (4139)Refutation not found, incomplete strategy% (4139)------------------------------
% 0.21/0.56  % (4139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4139)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4139)Memory used [KB]: 11129
% 0.21/0.56  % (4139)Time elapsed: 0.157 s
% 0.21/0.56  % (4139)------------------------------
% 0.21/0.56  % (4139)------------------------------
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f746,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f178,f334,f366,f707,f745])).
% 0.21/0.56  fof(f745,plain,(
% 0.21/0.56    ~spl4_1 | ~spl4_8),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f744])).
% 0.21/0.56  fof(f744,plain,(
% 0.21/0.56    $false | (~spl4_1 | ~spl4_8)),
% 0.21/0.56    inference(subsumption_resolution,[],[f743,f156])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    sK1 = k2_relat_1(sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f125,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f49,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.56    inference(negated_conjecture,[],[f19])).
% 0.21/0.56  fof(f19,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.56  % (4145)Refutation not found, incomplete strategy% (4145)------------------------------
% 0.21/0.56  % (4145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4145)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4145)Memory used [KB]: 10746
% 0.21/0.56  % (4145)Time elapsed: 0.159 s
% 0.21/0.56  % (4145)------------------------------
% 0.21/0.56  % (4145)------------------------------
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f55,f92])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 0.21/0.56  fof(f743,plain,(
% 0.21/0.56    sK1 != k2_relat_1(sK2) | (~spl4_1 | ~spl4_8)),
% 0.21/0.56    inference(subsumption_resolution,[],[f742,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 0.21/0.56  fof(f742,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | sK1 != k2_relat_1(sK2) | (~spl4_1 | ~spl4_8)),
% 0.21/0.56    inference(subsumption_resolution,[],[f741,f168])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    v1_relat_1(sK2) | ~spl4_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f167])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    spl4_1 <=> v1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.56  fof(f741,plain,(
% 0.21/0.56    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK1 != k2_relat_1(sK2) | ~spl4_8),
% 0.21/0.56    inference(subsumption_resolution,[],[f740,f100])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f84,f88])).
% 0.21/0.56  % (4157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.56  fof(f740,plain,(
% 0.21/0.56    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK1 != k2_relat_1(sK2) | ~spl4_8),
% 0.21/0.56    inference(superposition,[],[f365,f247])).
% 0.21/0.56  % (4154)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  fof(f247,plain,(
% 0.21/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.21/0.56    inference(global_subsumption,[],[f244,f246])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f245,f102])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f94,f88])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.56  fof(f245,plain,(
% 0.21/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.56    inference(resolution,[],[f233,f85])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(nnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.56  fof(f233,plain,(
% 0.21/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 0.21/0.56    inference(backward_demodulation,[],[f60,f208])).
% 0.21/0.56  fof(f208,plain,(
% 0.21/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f205,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    v1_funct_1(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.21/0.56    inference(resolution,[],[f128,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 1.54/0.56  % (4148)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.56  fof(f128,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f126,f53])).
% 1.54/0.56  fof(f126,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 1.54/0.56    inference(resolution,[],[f55,f91])).
% 1.54/0.56  fof(f91,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f44])).
% 1.54/0.56  fof(f44,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.56    inference(flattening,[],[f43])).
% 1.54/0.56  fof(f43,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.56    inference(ennf_transformation,[],[f16])).
% 1.54/0.56  fof(f16,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.54/0.56  fof(f60,plain,(
% 1.54/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.54/0.56    inference(cnf_transformation,[],[f50])).
% 1.54/0.56  fof(f244,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.56    inference(subsumption_resolution,[],[f243,f53])).
% 1.54/0.56  fof(f243,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.54/0.56    inference(subsumption_resolution,[],[f242,f55])).
% 1.54/0.56  fof(f242,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.54/0.56    inference(subsumption_resolution,[],[f241,f56])).
% 1.54/0.56  % (4149)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.54/0.56  fof(f241,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.54/0.56    inference(subsumption_resolution,[],[f236,f58])).
% 1.54/0.56  fof(f236,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.54/0.56    inference(superposition,[],[f90,f208])).
% 1.54/0.56  fof(f90,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f42,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.56    inference(flattening,[],[f41])).
% 1.54/0.56  fof(f41,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.56    inference(ennf_transformation,[],[f15])).
% 1.54/0.56  fof(f15,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.54/0.56  fof(f365,plain,(
% 1.54/0.56    ( ! [X1] : (~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X1) != sK1) ) | ~spl4_8),
% 1.54/0.56    inference(avatar_component_clause,[],[f364])).
% 1.54/0.56  fof(f364,plain,(
% 1.54/0.56    spl4_8 <=> ! [X1] : (k2_relat_1(X1) != sK1 | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK3)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.54/0.56  fof(f707,plain,(
% 1.54/0.56    ~spl4_1 | ~spl4_3 | ~spl4_5),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f706])).
% 1.54/0.56  fof(f706,plain,(
% 1.54/0.56    $false | (~spl4_1 | ~spl4_3 | ~spl4_5)),
% 1.54/0.56    inference(subsumption_resolution,[],[f705,f325])).
% 1.54/0.56  fof(f325,plain,(
% 1.54/0.56    v1_relat_1(sK3) | ~spl4_3),
% 1.54/0.56    inference(avatar_component_clause,[],[f324])).
% 1.54/0.56  fof(f324,plain,(
% 1.54/0.56    spl4_3 <=> v1_relat_1(sK3)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.54/0.56  fof(f705,plain,(
% 1.54/0.56    ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5)),
% 1.54/0.56    inference(subsumption_resolution,[],[f704,f56])).
% 1.54/0.57  % (4140)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.54/0.57  fof(f704,plain,(
% 1.54/0.57    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(subsumption_resolution,[],[f703,f64])).
% 1.54/0.57  fof(f64,plain,(
% 1.54/0.57    k2_funct_1(sK2) != sK3),
% 1.54/0.57    inference(cnf_transformation,[],[f50])).
% 1.54/0.57  fof(f703,plain,(
% 1.54/0.57    k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(subsumption_resolution,[],[f702,f164])).
% 1.54/0.57  fof(f164,plain,(
% 1.54/0.57    sK0 = k2_relat_1(sK3)),
% 1.54/0.57    inference(forward_demodulation,[],[f131,f148])).
% 1.54/0.57  fof(f148,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f147,f56])).
% 1.54/0.57  fof(f147,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f146,f57])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    v1_funct_2(sK3,sK1,sK0)),
% 1.54/0.57    inference(cnf_transformation,[],[f50])).
% 1.54/0.57  fof(f146,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f145,f58])).
% 1.54/0.57  fof(f145,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f144,f53])).
% 1.54/0.57  fof(f144,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f143,f54])).
% 1.54/0.57  fof(f54,plain,(
% 1.54/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f50])).
% 1.54/0.57  fof(f143,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f141,f55])).
% 1.54/0.57  fof(f141,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(resolution,[],[f60,f87])).
% 1.54/0.57  fof(f87,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f40])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.57    inference(flattening,[],[f39])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.57    inference(ennf_transformation,[],[f18])).
% 1.54/0.57  fof(f18,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.54/0.57  fof(f131,plain,(
% 1.54/0.57    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.54/0.57    inference(resolution,[],[f58,f92])).
% 1.54/0.57  fof(f702,plain,(
% 1.54/0.57    sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(trivial_inequality_removal,[],[f701])).
% 1.54/0.57  fof(f701,plain,(
% 1.54/0.57    k6_partfun1(sK1) != k6_partfun1(sK1) | sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(superposition,[],[f436,f684])).
% 1.54/0.57  fof(f684,plain,(
% 1.54/0.57    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(backward_demodulation,[],[f379,f681])).
% 1.54/0.57  fof(f681,plain,(
% 1.54/0.57    sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(subsumption_resolution,[],[f680,f168])).
% 1.54/0.57  fof(f680,plain,(
% 1.54/0.57    sK2 = k2_funct_1(sK3) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(subsumption_resolution,[],[f679,f53])).
% 1.54/0.57  fof(f679,plain,(
% 1.54/0.57    sK2 = k2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(subsumption_resolution,[],[f678,f156])).
% 1.54/0.57  fof(f678,plain,(
% 1.54/0.57    sK1 != k2_relat_1(sK2) | sK2 = k2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(trivial_inequality_removal,[],[f676])).
% 1.54/0.57  fof(f676,plain,(
% 1.54/0.57    k6_partfun1(sK0) != k6_partfun1(sK0) | sK1 != k2_relat_1(sK2) | sK2 = k2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(superposition,[],[f670,f247])).
% 1.54/0.57  fof(f670,plain,(
% 1.54/0.57    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,sK3) | k2_relat_1(X2) != sK1 | k2_funct_1(sK3) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(forward_demodulation,[],[f669,f164])).
% 1.54/0.57  fof(f669,plain,(
% 1.54/0.57    ( ! [X2] : (k2_relat_1(X2) != sK1 | k5_relat_1(X2,sK3) != k6_partfun1(k2_relat_1(sK3)) | k2_funct_1(sK3) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(subsumption_resolution,[],[f668,f325])).
% 1.54/0.57  fof(f668,plain,(
% 1.54/0.57    ( ! [X2] : (k2_relat_1(X2) != sK1 | k5_relat_1(X2,sK3) != k6_partfun1(k2_relat_1(sK3)) | k2_funct_1(sK3) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK3)) ) | ~spl4_5),
% 1.54/0.57    inference(subsumption_resolution,[],[f163,f344])).
% 1.54/0.57  fof(f344,plain,(
% 1.54/0.57    v2_funct_1(sK3) | ~spl4_5),
% 1.54/0.57    inference(avatar_component_clause,[],[f342])).
% 1.54/0.57  fof(f342,plain,(
% 1.54/0.57    spl4_5 <=> v2_funct_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.54/0.57  fof(f163,plain,(
% 1.54/0.57    ( ! [X2] : (k2_relat_1(X2) != sK1 | k5_relat_1(X2,sK3) != k6_partfun1(k2_relat_1(sK3)) | k2_funct_1(sK3) = X2 | ~v2_funct_1(sK3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK3)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f160,f56])).
% 1.54/0.57  fof(f160,plain,(
% 1.54/0.57    ( ! [X2] : (k2_relat_1(X2) != sK1 | k5_relat_1(X2,sK3) != k6_partfun1(k2_relat_1(sK3)) | k2_funct_1(sK3) = X2 | ~v2_funct_1(sK3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.54/0.57    inference(superposition,[],[f97,f157])).
% 1.54/0.57  fof(f157,plain,(
% 1.54/0.57    sK1 = k1_relat_1(sK3)),
% 1.54/0.57    inference(forward_demodulation,[],[f130,f123])).
% 1.54/0.57  fof(f123,plain,(
% 1.54/0.57    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.54/0.57    inference(global_subsumption,[],[f58,f122])).
% 1.54/0.57  fof(f122,plain,(
% 1.54/0.57    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.54/0.57    inference(subsumption_resolution,[],[f121,f62])).
% 1.54/0.57  fof(f62,plain,(
% 1.54/0.57    k1_xboole_0 != sK0),
% 1.54/0.57    inference(cnf_transformation,[],[f50])).
% 1.54/0.57  fof(f121,plain,(
% 1.54/0.57    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.54/0.57    inference(resolution,[],[f57,f75])).
% 1.54/0.57  fof(f75,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f51])).
% 1.54/0.57  fof(f51,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(nnf_transformation,[],[f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(flattening,[],[f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.54/0.57  fof(f130,plain,(
% 1.54/0.57    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 1.54/0.57    inference(resolution,[],[f58,f96])).
% 1.54/0.57  fof(f96,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f47,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.54/0.57  fof(f97,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f65,f88])).
% 1.54/0.57  fof(f65,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f24])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(flattening,[],[f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f9])).
% 1.54/0.57  fof(f9,axiom,(
% 1.54/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.54/0.57  fof(f379,plain,(
% 1.54/0.57    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(forward_demodulation,[],[f378,f157])).
% 1.54/0.57  fof(f378,plain,(
% 1.54/0.57    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | (~spl4_3 | ~spl4_5)),
% 1.54/0.57    inference(subsumption_resolution,[],[f377,f325])).
% 1.54/0.57  fof(f377,plain,(
% 1.54/0.57    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_5),
% 1.54/0.57    inference(subsumption_resolution,[],[f369,f56])).
% 1.54/0.57  fof(f369,plain,(
% 1.54/0.57    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_5),
% 1.54/0.57    inference(resolution,[],[f344,f99])).
% 1.54/0.57  fof(f99,plain,(
% 1.54/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f66,f88])).
% 1.54/0.57  fof(f66,plain,(
% 1.54/0.57    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f26])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(flattening,[],[f25])).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.54/0.57  fof(f436,plain,(
% 1.54/0.57    ( ! [X2] : (k5_relat_1(X2,sK2) != k6_partfun1(sK1) | k2_relat_1(X2) != sK0 | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl4_1),
% 1.54/0.57    inference(forward_demodulation,[],[f435,f156])).
% 1.54/0.57  fof(f435,plain,(
% 1.54/0.57    ( ! [X2] : (k2_relat_1(X2) != sK0 | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2) | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl4_1),
% 1.54/0.57    inference(subsumption_resolution,[],[f155,f168])).
% 1.54/0.57  fof(f155,plain,(
% 1.54/0.57    ( ! [X2] : (k2_relat_1(X2) != sK0 | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2) | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK2)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f154,f53])).
% 1.54/0.57  fof(f154,plain,(
% 1.54/0.57    ( ! [X2] : (k2_relat_1(X2) != sK0 | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2) | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f152,f61])).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    v2_funct_1(sK2)),
% 1.54/0.57    inference(cnf_transformation,[],[f50])).
% 1.54/0.57  fof(f152,plain,(
% 1.54/0.57    ( ! [X2] : (k2_relat_1(X2) != sK0 | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2) | k2_funct_1(sK2) = X2 | ~v2_funct_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.54/0.57    inference(superposition,[],[f97,f149])).
% 1.54/0.57  fof(f149,plain,(
% 1.54/0.57    sK0 = k1_relat_1(sK2)),
% 1.54/0.57    inference(forward_demodulation,[],[f124,f120])).
% 1.54/0.57  fof(f120,plain,(
% 1.54/0.57    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.54/0.57    inference(global_subsumption,[],[f55,f119])).
% 1.54/0.57  fof(f119,plain,(
% 1.54/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.54/0.57    inference(subsumption_resolution,[],[f118,f63])).
% 1.54/0.57  fof(f63,plain,(
% 1.54/0.57    k1_xboole_0 != sK1),
% 1.54/0.57    inference(cnf_transformation,[],[f50])).
% 1.54/0.57  fof(f118,plain,(
% 1.54/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.54/0.57    inference(resolution,[],[f54,f75])).
% 1.54/0.57  fof(f124,plain,(
% 1.54/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.54/0.57    inference(resolution,[],[f55,f96])).
% 1.54/0.57  fof(f366,plain,(
% 1.54/0.57    spl4_5 | spl4_8 | ~spl4_3),
% 1.54/0.57    inference(avatar_split_clause,[],[f359,f324,f364,f342])).
% 1.54/0.57  fof(f359,plain,(
% 1.54/0.57    ( ! [X1] : (k2_relat_1(X1) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl4_3),
% 1.54/0.57    inference(subsumption_resolution,[],[f162,f325])).
% 1.54/0.57  fof(f162,plain,(
% 1.54/0.57    ( ! [X1] : (k2_relat_1(X1) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK3)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f159,f56])).
% 1.54/0.57  fof(f159,plain,(
% 1.54/0.57    ( ! [X1] : (k2_relat_1(X1) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.54/0.57    inference(superposition,[],[f82,f157])).
% 1.54/0.57  fof(f82,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f36])).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(flattening,[],[f35])).
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.54/0.57  fof(f334,plain,(
% 1.54/0.57    spl4_3),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f333])).
% 1.54/0.57  fof(f333,plain,(
% 1.54/0.57    $false | spl4_3),
% 1.54/0.57    inference(subsumption_resolution,[],[f332,f95])).
% 1.54/0.57  fof(f95,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.54/0.57  fof(f332,plain,(
% 1.54/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_3),
% 1.54/0.57    inference(resolution,[],[f331,f58])).
% 1.54/0.57  fof(f331,plain,(
% 1.54/0.57    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_3),
% 1.54/0.57    inference(resolution,[],[f326,f93])).
% 1.54/0.57  fof(f93,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f46])).
% 1.54/0.57  fof(f46,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.54/0.57  fof(f326,plain,(
% 1.54/0.57    ~v1_relat_1(sK3) | spl4_3),
% 1.54/0.57    inference(avatar_component_clause,[],[f324])).
% 1.54/0.57  fof(f178,plain,(
% 1.54/0.57    spl4_1),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f177])).
% 1.54/0.57  fof(f177,plain,(
% 1.54/0.57    $false | spl4_1),
% 1.54/0.57    inference(subsumption_resolution,[],[f176,f95])).
% 1.54/0.57  fof(f176,plain,(
% 1.54/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 1.54/0.57    inference(resolution,[],[f175,f55])).
% 1.54/0.57  fof(f175,plain,(
% 1.54/0.57    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 1.54/0.57    inference(resolution,[],[f169,f93])).
% 1.54/0.57  fof(f169,plain,(
% 1.54/0.57    ~v1_relat_1(sK2) | spl4_1),
% 1.54/0.57    inference(avatar_component_clause,[],[f167])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (4153)------------------------------
% 1.54/0.57  % (4153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (4153)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (4153)Memory used [KB]: 11129
% 1.54/0.57  % (4153)Time elapsed: 0.144 s
% 1.54/0.57  % (4153)------------------------------
% 1.54/0.57  % (4153)------------------------------
% 1.54/0.57  % (4133)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.54/0.57  % (4128)Success in time 0.207 s
%------------------------------------------------------------------------------
