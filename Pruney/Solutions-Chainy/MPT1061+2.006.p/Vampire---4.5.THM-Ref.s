%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 719 expanded)
%              Number of leaves         :   29 ( 216 expanded)
%              Depth                    :   20
%              Number of atoms          :  549 (4314 expanded)
%              Number of equality atoms :  121 ( 455 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f135,f142,f183,f199,f284,f341,f343,f362,f553,f574])).

fof(f574,plain,
    ( spl5_3
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | spl5_3
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f209,f568])).

fof(f568,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f107,f158])).

fof(f158,plain,(
    ! [X2] : k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2) ),
    inference(subsumption_resolution,[],[f148,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
            | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
          & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
          & r1_tarski(sK1,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
          & v1_funct_2(X4,sK0,sK3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
          | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
        & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
        & r1_tarski(sK1,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        & v1_funct_2(X4,sK0,sK3)
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
        | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
      & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      & v1_funct_2(sK4,sK0,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

% (18318)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f148,plain,(
    ! [X2] :
      ( k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f54,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f209,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_12
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f553,plain,
    ( spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f551,f371])).

fof(f371,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f346,f369])).

% (18320)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f369,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f181,f214])).

fof(f214,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl5_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f181,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_9
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f346,plain,
    ( m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f173,f214])).

fof(f173,plain,(
    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f162,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f162,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(backward_demodulation,[],[f56,f149])).

fof(f149,plain,(
    ! [X3] : k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3) ),
    inference(resolution,[],[f54,f61])).

% (18322)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

% (18313)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f56,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f551,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f550,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f550,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f540,f499])).

fof(f499,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f446,f490])).

fof(f490,plain,
    ( k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f489,f371])).

fof(f489,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f479,f94])).

fof(f479,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f445,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f445,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f348,f432])).

fof(f432,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f364,f81])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f364,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f357,f94])).

fof(f357,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f301,f214])).

fof(f301,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl5_12 ),
    inference(resolution,[],[f209,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f348,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl5_2
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f200,f214])).

fof(f200,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(forward_demodulation,[],[f103,f158])).

fof(f103,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f446,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f350,f432])).

fof(f350,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f217,f214])).

fof(f217,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl5_14
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f540,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f498,f92])).

fof(f92,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f498,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f445,f490])).

fof(f362,plain,
    ( spl5_8
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | spl5_8
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f347,f82])).

fof(f82,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f347,plain,
    ( ~ r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1))
    | spl5_8
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f177,f214])).

fof(f177,plain,
    ( ~ r1_tarski(sK2,k9_relat_1(sK4,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_8
  <=> r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f343,plain,
    ( spl5_13
    | ~ spl5_14
    | spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f342,f208,f101,f216,f212])).

fof(f342,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f297,f200])).

fof(f297,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(resolution,[],[f209,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f341,plain,
    ( ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f339,f55])).

fof(f55,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f339,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(forward_demodulation,[],[f338,f163])).

fof(f163,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f152,f134])).

fof(f134,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_7
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f152,plain,(
    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f54,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f338,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f337,f153])).

fof(f153,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f54,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f337,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_12
    | spl5_14 ),
    inference(trivial_inequality_removal,[],[f336])).

fof(f336,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_12
    | spl5_14 ),
    inference(superposition,[],[f312,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f312,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f309,f209])).

fof(f309,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_14 ),
    inference(superposition,[],[f218,f77])).

fof(f218,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f216])).

fof(f284,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f282,f162])).

fof(f282,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | spl5_12 ),
    inference(forward_demodulation,[],[f281,f166])).

fof(f166,plain,(
    ! [X3] : k9_relat_1(sK4,X3) = k2_relat_1(k7_relat_1(sK4,X3)) ),
    inference(resolution,[],[f153,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f281,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f280,f258])).

fof(f258,plain,(
    ! [X11] : v1_relat_1(k7_relat_1(sK4,X11)) ),
    inference(resolution,[],[f160,f83])).

fof(f160,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(backward_demodulation,[],[f157,f158])).

fof(f157,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(subsumption_resolution,[],[f147,f52])).

fof(f147,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f280,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_12 ),
    inference(subsumption_resolution,[],[f278,f167])).

fof(f167,plain,(
    ! [X4] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X4)),X4) ),
    inference(resolution,[],[f153,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f278,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_12 ),
    inference(resolution,[],[f210,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f210,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f208])).

fof(f199,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f161,f159])).

fof(f159,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl5_1 ),
    inference(backward_demodulation,[],[f99,f158])).

fof(f99,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f161,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(backward_demodulation,[],[f156,f158])).

fof(f156,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) ),
    inference(subsumption_resolution,[],[f146,f52])).

fof(f146,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f54,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f183,plain,
    ( ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f172,f179,f175])).

fof(f172,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    inference(resolution,[],[f162,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f142,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f137,f73])).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f137,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f51,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f51,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f126,f132,f128])).

fof(f126,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f125,f54])).

fof(f125,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f53,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f108,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f57,f105,f101,f97])).

fof(f57,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (18324)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (18323)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (18317)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (18316)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (18333)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (18334)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (18324)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (18327)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (18325)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (18326)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (18332)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f577,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f108,f135,f142,f183,f199,f284,f341,f343,f362,f553,f574])).
% 0.21/0.52  fof(f574,plain,(
% 0.21/0.52    spl5_3 | ~spl5_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f573])).
% 0.21/0.52  fof(f573,plain,(
% 0.21/0.52    $false | (spl5_3 | ~spl5_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f568])).
% 0.21/0.52  fof(f568,plain,(
% 0.21/0.52    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 0.21/0.52    inference(forward_demodulation,[],[f107,f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X2] : (k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f148,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f43,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.21/0.52    inference(ennf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f21])).
% 0.21/0.52  fof(f21,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 0.21/0.52  % (18318)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ( ! [X2] : (k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2) | ~v1_funct_1(sK4)) )),
% 0.21/0.52    inference(resolution,[],[f54,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f208])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    spl5_12 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f553,plain,(
% 0.21/0.52    spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f552])).
% 0.21/0.52  fof(f552,plain,(
% 0.21/0.52    $false | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f551,f371])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl5_9 | ~spl5_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f346,f369])).
% 0.21/0.52  % (18320)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    k1_xboole_0 = k9_relat_1(sK4,sK1) | (~spl5_9 | ~spl5_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f181,f214])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f212])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    spl5_13 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    sK2 = k9_relat_1(sK4,sK1) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl5_9 <=> sK2 = k9_relat_1(sK4,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) | ~spl5_13),
% 0.21/0.52    inference(backward_demodulation,[],[f173,f214])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2))),
% 0.21/0.52    inference(resolution,[],[f162,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 0.21/0.52    inference(backward_demodulation,[],[f56,f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ( ! [X3] : (k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3)) )),
% 0.21/0.52    inference(resolution,[],[f54,f61])).
% 0.21/0.52  % (18322)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  % (18313)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f551,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f550,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f550,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f540,f499])).
% 0.21/0.52  fof(f499,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.21/0.52    inference(backward_demodulation,[],[f446,f490])).
% 0.21/0.52  fof(f490,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f489,f371])).
% 0.21/0.52  fof(f489,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f479,f94])).
% 0.21/0.52  fof(f479,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(resolution,[],[f445,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f445,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f348,f432])).
% 0.21/0.52  fof(f432,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK4,sK1) | (~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(resolution,[],[f364,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f357,f94])).
% 0.21/0.52  fof(f357,plain,(
% 0.21/0.52    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0)) | (~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f301,f214])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) | ~spl5_12),
% 0.21/0.52    inference(resolution,[],[f209,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f348,plain,(
% 0.21/0.52    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (spl5_2 | ~spl5_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f200,f214])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_2),
% 0.21/0.52    inference(forward_demodulation,[],[f103,f158])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f446,plain,(
% 0.21/0.52    sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0) | (~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.21/0.52    inference(backward_demodulation,[],[f350,f432])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1)) | (~spl5_13 | ~spl5_14)),
% 0.21/0.52    inference(backward_demodulation,[],[f217,f214])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f216])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    spl5_14 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.52  fof(f540,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(resolution,[],[f498,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f498,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f445,f490])).
% 0.21/0.52  fof(f362,plain,(
% 0.21/0.52    spl5_8 | ~spl5_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f361])).
% 0.21/0.52  fof(f361,plain,(
% 0.21/0.52    $false | (spl5_8 | ~spl5_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f347,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) | (spl5_8 | ~spl5_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f177,f214])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ~r1_tarski(sK2,k9_relat_1(sK4,sK1)) | spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    spl5_8 <=> r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    spl5_13 | ~spl5_14 | spl5_2 | ~spl5_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f342,f208,f101,f216,f212])).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | (spl5_2 | ~spl5_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f297,f200])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | ~spl5_12),
% 0.21/0.52    inference(resolution,[],[f209,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    ~spl5_7 | ~spl5_12 | spl5_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f340])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    $false | (~spl5_7 | ~spl5_12 | spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f339,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    r1_tarski(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK0) | (~spl5_7 | ~spl5_12 | spl5_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f338,f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK4) | ~spl5_7),
% 0.21/0.52    inference(forward_demodulation,[],[f152,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl5_7 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 0.21/0.52    inference(resolution,[],[f54,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    ~r1_tarski(sK1,k1_relat_1(sK4)) | (~spl5_12 | spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f337,f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    v1_relat_1(sK4)),
% 0.21/0.52    inference(resolution,[],[f54,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f337,plain,(
% 0.21/0.52    ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_12 | spl5_14)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f336])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    sK1 != sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_12 | spl5_14)),
% 0.21/0.52    inference(superposition,[],[f312,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_12 | spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f309,f209])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_14),
% 0.21/0.52    inference(superposition,[],[f218,f77])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f216])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    spl5_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f283])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    $false | spl5_12),
% 0.21/0.52    inference(subsumption_resolution,[],[f282,f162])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | spl5_12),
% 0.21/0.52    inference(forward_demodulation,[],[f281,f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ( ! [X3] : (k9_relat_1(sK4,X3) = k2_relat_1(k7_relat_1(sK4,X3))) )),
% 0.21/0.52    inference(resolution,[],[f153,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl5_12),
% 0.21/0.52    inference(subsumption_resolution,[],[f280,f258])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    ( ! [X11] : (v1_relat_1(k7_relat_1(sK4,X11))) )),
% 0.21/0.52    inference(resolution,[],[f160,f83])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(k7_relat_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f157,f158])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f147,f52])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) )),
% 0.21/0.52    inference(resolution,[],[f54,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_12),
% 0.21/0.52    inference(subsumption_resolution,[],[f278,f167])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ( ! [X4] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X4)),X4)) )),
% 0.21/0.52    inference(resolution,[],[f153,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_12),
% 0.21/0.52    inference(resolution,[],[f210,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f208])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    spl5_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f195])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    $false | spl5_1),
% 0.21/0.52    inference(resolution,[],[f161,f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl5_1),
% 0.21/0.52    inference(backward_demodulation,[],[f99,f158])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f156,f158])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f146,f52])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) | ~v1_funct_1(sK4)) )),
% 0.21/0.52    inference(resolution,[],[f54,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ~spl5_8 | spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f172,f179,f175])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    sK2 = k9_relat_1(sK4,sK1) | ~r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 0.21/0.52    inference(resolution,[],[f162,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ~spl5_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    $false | ~spl5_6),
% 0.21/0.52    inference(subsumption_resolution,[],[f137,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl5_6),
% 0.21/0.52    inference(backward_demodulation,[],[f51,f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl5_6 <=> k1_xboole_0 = sK3),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~v1_xboole_0(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl5_6 | spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f126,f132,f128])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f54])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.21/0.52    inference(resolution,[],[f53,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    v1_funct_2(sK4,sK0,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f57,f105,f101,f97])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (18324)------------------------------
% 0.21/0.52  % (18324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18324)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (18324)Memory used [KB]: 10874
% 0.21/0.52  % (18324)Time elapsed: 0.092 s
% 0.21/0.52  % (18324)------------------------------
% 0.21/0.52  % (18324)------------------------------
% 1.31/0.52  % (18312)Success in time 0.167 s
%------------------------------------------------------------------------------
