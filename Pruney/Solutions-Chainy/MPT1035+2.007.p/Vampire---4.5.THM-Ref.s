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
% DateTime   : Thu Dec  3 13:06:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 850 expanded)
%              Number of leaves         :   18 ( 208 expanded)
%              Depth                    :   19
%              Number of atoms          :  751 (4370 expanded)
%              Number of equality atoms :   92 (1170 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f902,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f69,f74,f79,f387,f391,f408,f444,f500,f540,f543,f578,f628,f901])).

fof(f901,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f900])).

fof(f900,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f899,f646])).

fof(f646,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f608,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f608,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,sK1,sK2))
    | ~ spl6_1
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f369,f56])).

fof(f56,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f369,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl6_20
  <=> r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f899,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f898,f64])).

fof(f64,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_3
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f898,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f897,f107])).

fof(f107,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f94,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f94,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

% (22216)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

fof(f897,plain,
    ( ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f896,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f896,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f873,f546])).

fof(f546,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f436,f527])).

fof(f527,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f525,f471])).

fof(f471,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f446,f56])).

fof(f446,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f27,f59])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f525,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f501,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f501,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f490,f470])).

fof(f470,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f445,f56])).

fof(f445,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f26,f59])).

fof(f26,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f490,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f471,f48])).

fof(f48,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f436,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl6_25
  <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f873,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(equality_resolution,[],[f720])).

fof(f720,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3))
        | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK3)
        | ~ r2_hidden(sK5(X1,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f719,f695])).

fof(f695,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f693,f667])).

fof(f667,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f632,f56])).

fof(f632,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f27,f59])).

fof(f693,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(superposition,[],[f651,f39])).

fof(f651,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f580,f59])).

fof(f580,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl6_1
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f443,f56])).

fof(f443,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl6_26
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f719,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3))
        | ~ v1_funct_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(sK3))
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK3)
        | ~ r2_hidden(sK5(X1,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f718,f25])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f718,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(sK3))
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK3)
        | ~ r2_hidden(sK5(X1,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f704,f88])).

fof(f88,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f85,f34])).

fof(f85,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f27,f30])).

fof(f704,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(sK3))
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK3)
        | ~ r2_hidden(sK5(X1,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f33,f473])).

fof(f473,plain,
    ( ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f448,f56])).

fof(f448,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relset_1(sK0,k1_xboole_0,sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f68,f59])).

fof(f68,plain,
    ( ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_4
  <=> ! [X4] :
        ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0)
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

fof(f628,plain,
    ( spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f626,f29])).

fof(f626,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f625,f609])).

fof(f609,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK2))
    | spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f430,f65])).

fof(f65,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f430,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r1_partfun1(sK2,sK3)
    | spl6_2
    | spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f429,f107])).

fof(f429,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | spl6_2
    | spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f428,f28])).

fof(f428,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | spl6_2
    | spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f173,f373])).

fof(f373,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl6_21
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f173,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | spl6_2
    | spl6_5 ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4)
        | ~ r1_tarski(k1_relat_1(X0),sK0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK4,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_partfun1(X0,sK3) )
    | spl6_2
    | spl6_5 ),
    inference(backward_demodulation,[],[f113,f126])).

fof(f126,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f124,f27])).

fof(f124,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_2 ),
    inference(superposition,[],[f87,f39])).

fof(f87,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f86,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f81,f60])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f27,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f113,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4)
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK3))
        | ~ r2_hidden(sK4,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_partfun1(X0,sK3) )
    | spl6_5 ),
    inference(subsumption_resolution,[],[f112,f25])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK3))
        | ~ r2_hidden(sK4,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_partfun1(X0,sK3) )
    | spl6_5 ),
    inference(subsumption_resolution,[],[f110,f88])).

fof(f110,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK3))
        | ~ r2_hidden(sK4,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_partfun1(X0,sK3) )
    | spl6_5 ),
    inference(superposition,[],[f73,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_5
  <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f625,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(superposition,[],[f78,f39])).

fof(f78,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_6
  <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f578,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f576,f65])).

fof(f576,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f575,f107])).

fof(f575,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f574,f558])).

fof(f558,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f554,f472])).

fof(f472,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f447,f56])).

fof(f447,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f29,f59])).

fof(f554,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(superposition,[],[f545,f39])).

fof(f545,plain,
    ( r2_hidden(sK4,k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f544,f56])).

fof(f544,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,k1_xboole_0,sK2))
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f78,f59])).

fof(f574,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f573,f28])).

fof(f573,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f565,f468])).

fof(f468,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_21 ),
    inference(backward_demodulation,[],[f373,f56])).

fof(f565,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(equality_resolution,[],[f528])).

fof(f528,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4)
        | ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK4,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(backward_demodulation,[],[f113,f527])).

fof(f543,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_21
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_21
    | spl6_25 ),
    inference(subsumption_resolution,[],[f541,f468])).

fof(f541,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_25 ),
    inference(forward_demodulation,[],[f437,f527])).

fof(f437,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f435])).

fof(f540,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_20 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_20 ),
    inference(subsumption_resolution,[],[f535,f464])).

fof(f464,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f91,f56])).

fof(f91,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f535,plain,
    ( ~ v4_relat_1(sK2,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_20 ),
    inference(backward_demodulation,[],[f505,f527])).

fof(f505,plain,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK3))
    | spl6_3
    | spl6_20 ),
    inference(subsumption_resolution,[],[f504,f107])).

fof(f504,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_relat_1(sK3))
    | spl6_3
    | spl6_20 ),
    inference(resolution,[],[f405,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f405,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | spl6_3
    | spl6_20 ),
    inference(subsumption_resolution,[],[f404,f64])).

fof(f404,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | r1_partfun1(sK2,sK3)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f403,f107])).

fof(f403,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f402,f25])).

fof(f402,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f401,f88])).

fof(f401,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f400,f28])).

fof(f400,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | spl6_20 ),
    inference(resolution,[],[f399,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0)
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f399,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | spl6_20 ),
    inference(subsumption_resolution,[],[f398,f29])).

fof(f398,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_20 ),
    inference(superposition,[],[f370,f39])).

fof(f370,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f368])).

fof(f500,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_26 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_26 ),
    inference(subsumption_resolution,[],[f498,f470])).

fof(f498,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_26 ),
    inference(subsumption_resolution,[],[f490,f487])).

fof(f487,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_26 ),
    inference(forward_demodulation,[],[f486,f56])).

fof(f486,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl6_2
    | spl6_26 ),
    inference(forward_demodulation,[],[f442,f59])).

fof(f442,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f441])).

fof(f444,plain,
    ( spl6_26
    | spl6_2 ),
    inference(avatar_split_clause,[],[f439,f58,f441])).

fof(f439,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f81,f26])).

fof(f408,plain,
    ( spl6_2
    | spl6_3
    | spl6_20
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl6_2
    | spl6_3
    | spl6_20
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f406,f373])).

fof(f406,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl6_2
    | spl6_3
    | spl6_20 ),
    inference(forward_demodulation,[],[f405,f126])).

fof(f391,plain,(
    spl6_21 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl6_21 ),
    inference(subsumption_resolution,[],[f389,f91])).

fof(f389,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl6_21 ),
    inference(subsumption_resolution,[],[f388,f107])).

fof(f388,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl6_21 ),
    inference(resolution,[],[f374,f36])).

fof(f374,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f372])).

fof(f387,plain,
    ( ~ spl6_20
    | ~ spl6_21
    | spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f386,f67,f63,f58,f372,f368])).

fof(f386,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2))
    | spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f385,f64])).

fof(f385,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | r1_partfun1(sK2,sK3)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2))
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f384,f107])).

fof(f384,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2))
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f343,f28])).

fof(f343,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2))
    | spl6_2
    | ~ spl6_4 ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3))
        | ~ r1_tarski(k1_relat_1(X1),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK3)
        | ~ r2_hidden(sK5(X1,sK3),k1_relset_1(sK0,sK1,sK2)) )
    | spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f159,f126])).

fof(f159,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3))
        | ~ v1_funct_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(sK3))
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK3)
        | ~ r2_hidden(sK5(X1,sK3),k1_relset_1(sK0,sK1,sK2)) )
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f158,f25])).

fof(f158,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(sK3))
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK3)
        | ~ r2_hidden(sK5(X1,sK3),k1_relset_1(sK0,sK1,sK2)) )
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f144,f88])).

fof(f144,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(sK3))
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK3)
        | ~ r2_hidden(sK5(X1,sK3),k1_relset_1(sK0,sK1,sK2)) )
    | ~ spl6_4 ),
    inference(superposition,[],[f33,f68])).

fof(f79,plain,
    ( ~ spl6_3
    | spl6_6 ),
    inference(avatar_split_clause,[],[f21,f76,f63])).

fof(f21,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,
    ( ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f22,f71,f63])).

fof(f22,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f23,f67,f63])).

fof(f23,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f24,f58,f54])).

fof(f24,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:48:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (22234)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (22234)Refutation not found, incomplete strategy% (22234)------------------------------
% 0.21/0.44  % (22234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (22234)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (22234)Memory used [KB]: 10618
% 0.21/0.44  % (22234)Time elapsed: 0.027 s
% 0.21/0.44  % (22234)------------------------------
% 0.21/0.44  % (22234)------------------------------
% 0.21/0.46  % (22215)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (22228)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (22223)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (22218)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (22219)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (22214)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (22226)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (22217)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (22220)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (22233)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (22215)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f902,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f61,f69,f74,f79,f387,f391,f408,f444,f500,f540,f543,f578,f628,f901])).
% 0.21/0.49  fof(f901,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_20 | ~spl6_25 | ~spl6_26),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f900])).
% 0.21/0.49  fof(f900,plain,(
% 0.21/0.49    $false | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_20 | ~spl6_25 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f899,f646])).
% 0.21/0.49  fof(f646,plain,(
% 0.21/0.49    r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_20)),
% 0.21/0.49    inference(forward_demodulation,[],[f608,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f608,plain,(
% 0.21/0.49    r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,sK1,sK2)) | (~spl6_1 | ~spl6_20)),
% 0.21/0.49    inference(forward_demodulation,[],[f369,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl6_1 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2)) | ~spl6_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f368])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    spl6_20 <=> r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.49  fof(f899,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_25 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f898,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~r1_partfun1(sK2,sK3) | spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl6_3 <=> r1_partfun1(sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f898,plain,(
% 0.21/0.49    r1_partfun1(sK2,sK3) | ~r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_25 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f897,f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f29,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  % (22216)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).
% 0.21/0.49  fof(f897,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | ~r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_25 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f896,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f896,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | ~r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_25 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f873,f546])).
% 0.21/0.49  fof(f546,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (~spl6_1 | ~spl6_2 | ~spl6_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f436,f527])).
% 0.21/0.49  fof(f527,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK3) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f525,f471])).
% 0.21/0.49  fof(f471,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(backward_demodulation,[],[f446,f56])).
% 0.21/0.49  fof(f446,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 0.21/0.49    inference(backward_demodulation,[],[f27,f59])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f525,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(superposition,[],[f501,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f501,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f490,f470])).
% 0.21/0.49  fof(f470,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(backward_demodulation,[],[f445,f56])).
% 0.21/0.49  fof(f445,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl6_2),
% 0.21/0.49    inference(backward_demodulation,[],[f26,f59])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f490,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(resolution,[],[f471,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f436,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~spl6_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f435])).
% 0.21/0.49  fof(f435,plain,(
% 0.21/0.49    spl6_25 <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.49  fof(f873,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | ~r2_hidden(sK5(sK2,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_26)),
% 0.21/0.49    inference(equality_resolution,[],[f720])).
% 0.21/0.49  fof(f720,plain,(
% 0.21/0.49    ( ! [X1] : (k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3)) | ~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_partfun1(X1,sK3) | ~r2_hidden(sK5(X1,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))) ) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_26)),
% 0.21/0.49    inference(forward_demodulation,[],[f719,f695])).
% 0.21/0.49  fof(f695,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK3) | (~spl6_1 | ~spl6_2 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f693,f667])).
% 0.21/0.49  fof(f667,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(backward_demodulation,[],[f632,f56])).
% 0.21/0.49  fof(f632,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 0.21/0.49    inference(backward_demodulation,[],[f27,f59])).
% 0.21/0.49  fof(f693,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_1 | ~spl6_2 | ~spl6_26)),
% 0.21/0.49    inference(superposition,[],[f651,f39])).
% 0.21/0.49  fof(f651,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_26)),
% 0.21/0.49    inference(forward_demodulation,[],[f580,f59])).
% 0.21/0.49  fof(f580,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl6_1 | ~spl6_26)),
% 0.21/0.49    inference(forward_demodulation,[],[f443,f56])).
% 0.21/0.49  fof(f443,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f441])).
% 0.21/0.49  fof(f441,plain,(
% 0.21/0.49    spl6_26 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.49  fof(f719,plain,(
% 0.21/0.49    ( ! [X1] : (k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3)) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(sK3)) | ~v1_relat_1(X1) | r1_partfun1(X1,sK3) | ~r2_hidden(sK5(X1,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))) ) | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f718,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f718,plain,(
% 0.21/0.49    ( ! [X1] : (k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3)) | ~v1_funct_1(X1) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(sK3)) | ~v1_relat_1(X1) | r1_partfun1(X1,sK3) | ~r2_hidden(sK5(X1,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))) ) | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f704,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f34])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f27,f30])).
% 0.21/0.49  fof(f704,plain,(
% 0.21/0.49    ( ! [X1] : (k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(sK3)) | ~v1_relat_1(X1) | r1_partfun1(X1,sK3) | ~r2_hidden(sK5(X1,sK3),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))) ) | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(superposition,[],[f33,f473])).
% 0.21/0.49  fof(f473,plain,(
% 0.21/0.49    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))) ) | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f448,f56])).
% 0.21/0.49  fof(f448,plain,(
% 0.21/0.49    ( ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,k1_xboole_0,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) ) | (~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f68,f59])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) ) | ~spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl6_4 <=> ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0) | r1_partfun1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).
% 0.21/0.49  fof(f628,plain,(
% 0.21/0.49    spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_21),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f627])).
% 0.21/0.49  fof(f627,plain,(
% 0.21/0.49    $false | (spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f626,f29])).
% 0.21/0.49  fof(f626,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f625,f609])).
% 0.21/0.49  fof(f609,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k1_relat_1(sK2)) | (spl6_2 | ~spl6_3 | spl6_5 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f430,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    r1_partfun1(sK2,sK3) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f430,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | (spl6_2 | spl6_5 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f429,f107])).
% 0.21/0.49  fof(f429,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_partfun1(sK2,sK3) | (spl6_2 | spl6_5 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f428,f28])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_partfun1(sK2,sK3) | (spl6_2 | spl6_5 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f173,f373])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK2),sK0) | ~spl6_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f372])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    spl6_21 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_partfun1(sK2,sK3) | (spl6_2 | spl6_5)),
% 0.21/0.49    inference(equality_resolution,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0] : (k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4) | ~r1_tarski(k1_relat_1(X0),sK0) | ~v1_funct_1(X0) | ~r2_hidden(sK4,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_partfun1(X0,sK3)) ) | (spl6_2 | spl6_5)),
% 0.21/0.49    inference(backward_demodulation,[],[f113,f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | spl6_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f27])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_2),
% 0.21/0.49    inference(superposition,[],[f87,f39])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | spl6_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f26])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | spl6_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f81,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f27,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0] : (k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(sK3)) | ~r2_hidden(sK4,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_partfun1(X0,sK3)) ) | spl6_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f25])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4) | ~v1_funct_1(X0) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(sK3)) | ~r2_hidden(sK4,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_partfun1(X0,sK3)) ) | spl6_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f88])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(sK3)) | ~r2_hidden(sK4,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_partfun1(X0,sK3)) ) | spl6_5),
% 0.21/0.49    inference(superposition,[],[f73,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_partfun1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl6_5 <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f625,plain,(
% 0.21/0.49    r2_hidden(sK4,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.21/0.49    inference(superposition,[],[f78,f39])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl6_6 <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f578,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_21),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f577])).
% 0.21/0.49  fof(f577,plain,(
% 0.21/0.49    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f576,f65])).
% 0.21/0.49  fof(f576,plain,(
% 0.21/0.49    ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | spl6_5 | ~spl6_6 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f575,f107])).
% 0.21/0.49  fof(f575,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | spl6_5 | ~spl6_6 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f574,f558])).
% 0.21/0.49  fof(f558,plain,(
% 0.21/0.49    r2_hidden(sK4,k1_relat_1(sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f554,f472])).
% 0.21/0.49  fof(f472,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(backward_demodulation,[],[f447,f56])).
% 0.21/0.49  fof(f447,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 0.21/0.49    inference(backward_demodulation,[],[f29,f59])).
% 0.21/0.49  fof(f554,plain,(
% 0.21/0.49    r2_hidden(sK4,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_1 | ~spl6_2 | ~spl6_6)),
% 0.21/0.49    inference(superposition,[],[f545,f39])).
% 0.21/0.49  fof(f545,plain,(
% 0.21/0.49    r2_hidden(sK4,k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_6)),
% 0.21/0.49    inference(forward_demodulation,[],[f544,f56])).
% 0.21/0.49  fof(f544,plain,(
% 0.21/0.49    r2_hidden(sK4,k1_relset_1(sK0,k1_xboole_0,sK2)) | (~spl6_2 | ~spl6_6)),
% 0.21/0.49    inference(forward_demodulation,[],[f78,f59])).
% 0.21/0.49  fof(f574,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | spl6_5 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f573,f28])).
% 0.21/0.49  fof(f573,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | spl6_5 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f565,f468])).
% 0.21/0.49  fof(f468,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (~spl6_1 | ~spl6_21)),
% 0.21/0.49    inference(backward_demodulation,[],[f373,f56])).
% 0.21/0.49  fof(f565,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | ~v1_funct_1(sK2) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | spl6_5)),
% 0.21/0.49    inference(equality_resolution,[],[f528])).
% 0.21/0.49  fof(f528,plain,(
% 0.21/0.49    ( ! [X0] : (k1_funct_1(sK2,sK4) != k1_funct_1(X0,sK4) | ~r1_tarski(k1_relat_1(X0),k1_xboole_0) | ~v1_funct_1(X0) | ~r2_hidden(sK4,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_partfun1(X0,sK3)) ) | (~spl6_1 | ~spl6_2 | spl6_5)),
% 0.21/0.49    inference(backward_demodulation,[],[f113,f527])).
% 0.21/0.49  fof(f543,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_2 | ~spl6_21 | spl6_25),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f542])).
% 0.21/0.49  fof(f542,plain,(
% 0.21/0.49    $false | (~spl6_1 | ~spl6_2 | ~spl6_21 | spl6_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f541,f468])).
% 0.21/0.49  fof(f541,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f437,f527])).
% 0.21/0.49  fof(f437,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | spl6_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f435])).
% 0.21/0.49  fof(f540,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_2 | spl6_3 | spl6_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f539])).
% 0.21/0.49  fof(f539,plain,(
% 0.21/0.49    $false | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f535,f464])).
% 0.21/0.49  fof(f464,plain,(
% 0.21/0.49    v4_relat_1(sK2,k1_xboole_0) | ~spl6_1),
% 0.21/0.49    inference(backward_demodulation,[],[f91,f56])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    v4_relat_1(sK2,sK0)),
% 0.21/0.49    inference(resolution,[],[f29,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f535,plain,(
% 0.21/0.49    ~v4_relat_1(sK2,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_20)),
% 0.21/0.49    inference(backward_demodulation,[],[f505,f527])).
% 0.21/0.49  fof(f505,plain,(
% 0.21/0.49    ~v4_relat_1(sK2,k1_relat_1(sK3)) | (spl6_3 | spl6_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f504,f107])).
% 0.21/0.49  fof(f504,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,k1_relat_1(sK3)) | (spl6_3 | spl6_20)),
% 0.21/0.49    inference(resolution,[],[f405,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.49  fof(f405,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | (spl6_3 | spl6_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f404,f64])).
% 0.21/0.49  fof(f404,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | r1_partfun1(sK2,sK3) | spl6_20),
% 0.21/0.49    inference(subsumption_resolution,[],[f403,f107])).
% 0.21/0.49  fof(f403,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | spl6_20),
% 0.21/0.49    inference(subsumption_resolution,[],[f402,f25])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | spl6_20),
% 0.21/0.49    inference(subsumption_resolution,[],[f401,f88])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | spl6_20),
% 0.21/0.49    inference(subsumption_resolution,[],[f400,f28])).
% 0.21/0.49  fof(f400,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | spl6_20),
% 0.21/0.49    inference(resolution,[],[f399,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0) | r1_partfun1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    ~r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | spl6_20),
% 0.21/0.50    inference(subsumption_resolution,[],[f398,f29])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    ~r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_20),
% 0.21/0.50    inference(superposition,[],[f370,f39])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    ~r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2)) | spl6_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f368])).
% 0.21/0.50  fof(f500,plain,(
% 0.21/0.50    ~spl6_1 | ~spl6_2 | spl6_26),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f499])).
% 0.21/0.50  fof(f499,plain,(
% 0.21/0.50    $false | (~spl6_1 | ~spl6_2 | spl6_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f498,f470])).
% 0.21/0.50  fof(f498,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f490,f487])).
% 0.21/0.50  fof(f487,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_1 | ~spl6_2 | spl6_26)),
% 0.21/0.50    inference(forward_demodulation,[],[f486,f56])).
% 0.21/0.50  fof(f486,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl6_2 | spl6_26)),
% 0.21/0.50    inference(forward_demodulation,[],[f442,f59])).
% 0.21/0.50  fof(f442,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK1,sK3) | spl6_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f441])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    spl6_26 | spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f439,f58,f441])).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f81,f26])).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    spl6_2 | spl6_3 | spl6_20 | ~spl6_21),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f407])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    $false | (spl6_2 | spl6_3 | spl6_20 | ~spl6_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f406,f373])).
% 0.21/0.50  fof(f406,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl6_2 | spl6_3 | spl6_20)),
% 0.21/0.50    inference(forward_demodulation,[],[f405,f126])).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    spl6_21),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f390])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    $false | spl6_21),
% 0.21/0.50    inference(subsumption_resolution,[],[f389,f91])).
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    ~v4_relat_1(sK2,sK0) | spl6_21),
% 0.21/0.50    inference(subsumption_resolution,[],[f388,f107])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl6_21),
% 0.21/0.50    inference(resolution,[],[f374,f36])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | spl6_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f372])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    ~spl6_20 | ~spl6_21 | spl6_2 | spl6_3 | ~spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f386,f67,f63,f58,f372,f368])).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | ~r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2)) | (spl6_2 | spl6_3 | ~spl6_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f385,f64])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | r1_partfun1(sK2,sK3) | ~r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2)) | (spl6_2 | ~spl6_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f384,f107])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | ~r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2)) | (spl6_2 | ~spl6_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f343,f28])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | ~r2_hidden(sK5(sK2,sK3),k1_relset_1(sK0,sK1,sK2)) | (spl6_2 | ~spl6_4)),
% 0.21/0.50    inference(equality_resolution,[],[f160])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ( ! [X1] : (k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3)) | ~r1_tarski(k1_relat_1(X1),sK0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_partfun1(X1,sK3) | ~r2_hidden(sK5(X1,sK3),k1_relset_1(sK0,sK1,sK2))) ) | (spl6_2 | ~spl6_4)),
% 0.21/0.50    inference(forward_demodulation,[],[f159,f126])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ( ! [X1] : (k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3)) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(sK3)) | ~v1_relat_1(X1) | r1_partfun1(X1,sK3) | ~r2_hidden(sK5(X1,sK3),k1_relset_1(sK0,sK1,sK2))) ) | ~spl6_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f158,f25])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X1] : (k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3)) | ~v1_funct_1(X1) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(sK3)) | ~v1_relat_1(X1) | r1_partfun1(X1,sK3) | ~r2_hidden(sK5(X1,sK3),k1_relset_1(sK0,sK1,sK2))) ) | ~spl6_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f144,f88])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ( ! [X1] : (k1_funct_1(sK2,sK5(X1,sK3)) != k1_funct_1(X1,sK5(X1,sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(sK3)) | ~v1_relat_1(X1) | r1_partfun1(X1,sK3) | ~r2_hidden(sK5(X1,sK3),k1_relset_1(sK0,sK1,sK2))) ) | ~spl6_4),
% 0.21/0.50    inference(superposition,[],[f33,f68])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~spl6_3 | spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f76,f63])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~spl6_3 | ~spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f71,f63])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl6_3 | spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f67,f63])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl6_1 | ~spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f58,f54])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (22215)------------------------------
% 0.21/0.50  % (22215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22215)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (22215)Memory used [KB]: 11001
% 0.21/0.50  % (22215)Time elapsed: 0.058 s
% 0.21/0.50  % (22215)------------------------------
% 0.21/0.50  % (22215)------------------------------
% 0.21/0.50  % (22225)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (22213)Success in time 0.139 s
%------------------------------------------------------------------------------
