%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  204 (1133 expanded)
%              Number of leaves         :   22 ( 354 expanded)
%              Depth                    :   22
%              Number of atoms          :  828 (7232 expanded)
%              Number of equality atoms :  180 (1568 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f903,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f126,f128,f202,f207,f246,f409,f429,f448,f580,f590,f605,f631,f758,f902])).

fof(f902,plain,
    ( ~ spl10_3
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f901])).

fof(f901,plain,
    ( $false
    | ~ spl10_3
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f900,f737])).

fof(f737,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f93,f112])).

fof(f112,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl10_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f93,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f54,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f900,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f899,f713])).

fof(f713,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f132,f206])).

% (19141)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f206,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl10_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f132,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f57,f75])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f899,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f898,f92])).

fof(f92,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f54,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f898,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f897,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f897,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f896,f131])).

fof(f131,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f57,f74])).

fof(f896,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f895,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f895,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f894,f196])).

fof(f196,plain,
    ( sK2 != sK3
    | spl10_7 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl10_7
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f894,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_8 ),
    inference(trivial_inequality_removal,[],[f893])).

fof(f893,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_8 ),
    inference(superposition,[],[f62,f812])).

fof(f812,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl10_8 ),
    inference(resolution,[],[f201,f58])).

fof(f58,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f201,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl10_8
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f758,plain,
    ( ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f757])).

fof(f757,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f756,f125])).

fof(f125,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl10_6
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f756,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl10_7 ),
    inference(forward_demodulation,[],[f59,f197])).

fof(f197,plain,
    ( sK2 = sK3
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f195])).

fof(f59,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f631,plain,
    ( ~ spl10_8
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f629,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f629,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(resolution,[],[f606,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f606,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f201,f245])).

fof(f245,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl10_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f605,plain,
    ( spl10_3
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | spl10_3
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f603,f591])).

fof(f591,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f505,f472])).

fof(f472,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f208,f245])).

fof(f208,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f53,f116])).

fof(f116,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl10_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f505,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(resolution,[],[f471,f88])).

fof(f88,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

% (19142)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f471,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f209,f245])).

fof(f209,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f54,f116])).

fof(f603,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl10_3
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f602,f245])).

fof(f602,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl10_3
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f111,f116])).

fof(f111,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f590,plain,
    ( ~ spl10_4
    | spl10_9
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl10_4
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f588,f581])).

fof(f581,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f489,f465])).

fof(f465,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f210,f245])).

fof(f210,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f56,f116])).

fof(f56,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f489,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(resolution,[],[f464,f88])).

fof(f464,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f211,f245])).

% (19137)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f211,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f57,f116])).

fof(f588,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_4
    | spl10_9
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f587,f245])).

fof(f587,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl10_4
    | spl10_9 ),
    inference(forward_demodulation,[],[f205,f116])).

fof(f205,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f204])).

fof(f580,plain,
    ( ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f578,f131])).

fof(f578,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f577,f55])).

fof(f577,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f576,f196])).

fof(f576,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f575,f485])).

fof(f485,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | spl10_8
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f200,f245])).

fof(f200,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK0)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f199])).

fof(f575,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(trivial_inequality_removal,[],[f574])).

fof(f574,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(superposition,[],[f522,f461])).

fof(f461,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f460,f454])).

fof(f454,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(backward_demodulation,[],[f351,f245])).

fof(f351,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f206,f116])).

fof(f460,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f217,f245])).

fof(f217,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f132,f116])).

fof(f522,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK2,X1),k1_xboole_0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f521,f92])).

% (19163)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f521,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK2,X1),k1_xboole_0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f518,f52])).

fof(f518,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK2,X1),k1_xboole_0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(superposition,[],[f61,f456])).

fof(f456,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(backward_demodulation,[],[f451,f245])).

fof(f451,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f450,f449])).

fof(f449,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f112,f116])).

fof(f450,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f93,f116])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f448,plain,
    ( ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f446,f60])).

fof(f446,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(resolution,[],[f431,f63])).

fof(f431,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f430,f241])).

fof(f241,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl10_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f430,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f201,f286])).

fof(f286,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f282,f261])).

fof(f261,plain,
    ( k1_xboole_0 != sK3
    | spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f196,f241])).

fof(f282,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f273,f210])).

fof(f273,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl10_4 ),
    inference(resolution,[],[f211,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f429,plain,
    ( spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f427,f410])).

fof(f410,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f363,f306])).

fof(f306,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f263,f286])).

fof(f263,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f208,f241])).

fof(f363,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f307,f88])).

fof(f307,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f264,f286])).

fof(f264,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f209,f241])).

fof(f427,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f426,f286])).

fof(f426,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl10_3
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f425,f116])).

fof(f425,plain,
    ( sK0 != k1_relset_1(sK0,sK1,k1_xboole_0)
    | spl10_3
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f111,f241])).

fof(f409,plain,
    ( ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f407,f131])).

fof(f407,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f406,f55])).

fof(f406,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f405,f261])).

fof(f405,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f404,f305])).

fof(f305,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl10_4
    | spl10_7
    | spl10_8
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f262,f286])).

fof(f262,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0,sK3),sK0)
    | spl10_8
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f200,f241])).

fof(f404,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0)
    | k1_xboole_0 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(trivial_inequality_removal,[],[f403])).

fof(f403,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0)
    | k1_xboole_0 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(superposition,[],[f319,f348])).

fof(f348,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f293,f345])).

fof(f345,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f334,f290])).

fof(f290,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f210,f286])).

fof(f334,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f291,f88])).

fof(f291,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f211,f286])).

fof(f293,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f217,f286])).

% (19139)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f319,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(k1_xboole_0,X1),k1_xboole_0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f311,f286])).

fof(f311,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | k1_xboole_0 = X1
        | r2_hidden(sK4(k1_xboole_0,X1),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f268,f286])).

fof(f268,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | r2_hidden(sK4(k1_xboole_0,X1),sK0)
        | k1_relat_1(X1) != sK0
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl10_3
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f257,f241])).

fof(f257,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(k1_xboole_0,X1),sK0)
        | k1_relat_1(X1) != sK0
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl10_3
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f157,f241])).

fof(f157,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f156,f92])).

% (19162)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f156,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f153,f52])).

fof(f153,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_3 ),
    inference(superposition,[],[f61,f129])).

fof(f129,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f93,f112])).

fof(f246,plain,
    ( spl10_10
    | spl10_11
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f237,f114,f243,f239])).

fof(f237,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f228,f208])).

fof(f228,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl10_4 ),
    inference(resolution,[],[f209,f86])).

fof(f207,plain,
    ( spl10_9
    | spl10_4 ),
    inference(avatar_split_clause,[],[f138,f114,f204])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f134,f56])).

fof(f134,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f57,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f202,plain,
    ( spl10_7
    | spl10_8
    | ~ spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f193,f114,f110,f199,f195])).

fof(f193,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ spl10_3
    | spl10_4 ),
    inference(subsumption_resolution,[],[f192,f131])).

fof(f192,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | spl10_4 ),
    inference(subsumption_resolution,[],[f191,f55])).

fof(f191,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | spl10_4 ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_3
    | spl10_4 ),
    inference(superposition,[],[f157,f140])).

fof(f140,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl10_4 ),
    inference(backward_demodulation,[],[f132,f139])).

fof(f139,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl10_4 ),
    inference(subsumption_resolution,[],[f138,f115])).

fof(f115,plain,
    ( k1_xboole_0 != sK1
    | spl10_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f128,plain,(
    ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f121,f98])).

% (19164)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f98,plain,(
    ~ sP9(sK1,sK0) ),
    inference(resolution,[],[f54,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP9(X1,X0) ) ),
    inference(general_splitting,[],[f83,f89_D])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP9(X1,X0) ) ),
    inference(cnf_transformation,[],[f89_D])).

fof(f89_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP9(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

% (19165)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f121,plain,
    ( sP9(sK1,sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl10_5
  <=> sP9(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f126,plain,
    ( spl10_5
    | spl10_6 ),
    inference(avatar_split_clause,[],[f97,f123,f119])).

fof(f97,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP9(sK1,sK0) ),
    inference(resolution,[],[f54,f89])).

fof(f117,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f108,f114,f110])).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f95,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f54,f77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n020.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 09:25:07 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.52  % (19136)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (19144)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (19143)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (19151)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (19158)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (19159)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (19150)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (19148)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (19152)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (19140)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (19138)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (19144)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f903,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f117,f126,f128,f202,f207,f246,f409,f429,f448,f580,f590,f605,f631,f758,f902])).
% 0.22/0.54  fof(f902,plain,(
% 0.22/0.54    ~spl10_3 | spl10_7 | ~spl10_8 | ~spl10_9),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f901])).
% 0.22/0.54  fof(f901,plain,(
% 0.22/0.54    $false | (~spl10_3 | spl10_7 | ~spl10_8 | ~spl10_9)),
% 0.22/0.54    inference(subsumption_resolution,[],[f900,f737])).
% 0.22/0.54  fof(f737,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK2) | ~spl10_3),
% 0.22/0.54    inference(backward_demodulation,[],[f93,f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl10_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    spl10_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f54,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f33,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.54    inference(negated_conjecture,[],[f14])).
% 0.22/0.54  fof(f14,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 0.22/0.54  fof(f900,plain,(
% 0.22/0.54    sK0 != k1_relat_1(sK2) | (spl10_7 | ~spl10_8 | ~spl10_9)),
% 0.22/0.54    inference(forward_demodulation,[],[f899,f713])).
% 0.22/0.54  fof(f713,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK3) | ~spl10_9),
% 0.22/0.54    inference(forward_demodulation,[],[f132,f206])).
% 0.22/0.54  % (19141)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl10_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f204])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    spl10_9 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f57,f75])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f899,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | (spl10_7 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f898,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f54,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f898,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (spl10_7 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f897,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f897,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl10_7 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f896,f131])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f57,f74])).
% 0.22/0.55  fof(f896,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl10_7 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f895,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f895,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl10_7 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f894,f196])).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    sK2 != sK3 | spl10_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f195])).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    spl10_7 <=> sK2 = sK3),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.55  fof(f894,plain,(
% 0.22/0.55    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl10_8),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f893])).
% 0.22/0.55  fof(f893,plain,(
% 0.22/0.55    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl10_8),
% 0.22/0.55    inference(superposition,[],[f62,f812])).
% 0.22/0.55  fof(f812,plain,(
% 0.22/0.55    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl10_8),
% 0.22/0.55    inference(resolution,[],[f201,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f201,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2,sK3),sK0) | ~spl10_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f199])).
% 0.22/0.55  fof(f199,plain,(
% 0.22/0.55    spl10_8 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.55  fof(f758,plain,(
% 0.22/0.55    ~spl10_6 | ~spl10_7),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f757])).
% 0.22/0.55  fof(f757,plain,(
% 0.22/0.55    $false | (~spl10_6 | ~spl10_7)),
% 0.22/0.55    inference(subsumption_resolution,[],[f756,f125])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl10_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f123])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    spl10_6 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.55  fof(f756,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl10_7),
% 0.22/0.55    inference(forward_demodulation,[],[f59,f197])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    sK2 = sK3 | ~spl10_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f195])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f631,plain,(
% 0.22/0.55    ~spl10_8 | ~spl10_11),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f630])).
% 0.22/0.55  fof(f630,plain,(
% 0.22/0.55    $false | (~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f629,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f629,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0) | (~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(resolution,[],[f606,f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.55    inference(rectify,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.55    inference(nnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.55  fof(f606,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | (~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f201,f245])).
% 0.22/0.55  fof(f245,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | ~spl10_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f243])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    spl10_11 <=> k1_xboole_0 = sK0),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.22/0.55  fof(f605,plain,(
% 0.22/0.55    spl10_3 | ~spl10_4 | ~spl10_11),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f604])).
% 0.22/0.55  fof(f604,plain,(
% 0.22/0.55    $false | (spl10_3 | ~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f603,f591])).
% 0.22/0.55  fof(f591,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f505,f472])).
% 0.22/0.55  fof(f472,plain,(
% 0.22/0.55    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f208,f245])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl10_4),
% 0.22/0.55    inference(backward_demodulation,[],[f53,f116])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl10_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f114])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    spl10_4 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f505,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(resolution,[],[f471,f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.55    inference(equality_resolution,[],[f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  % (19142)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f471,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f209,f245])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl10_4),
% 0.22/0.55    inference(backward_demodulation,[],[f54,f116])).
% 0.22/0.55  fof(f603,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl10_3 | ~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f602,f245])).
% 0.22/0.55  fof(f602,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl10_3 | ~spl10_4)),
% 0.22/0.55    inference(forward_demodulation,[],[f111,f116])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,sK1,sK2) | spl10_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f110])).
% 0.22/0.55  fof(f590,plain,(
% 0.22/0.55    ~spl10_4 | spl10_9 | ~spl10_11),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f589])).
% 0.22/0.55  fof(f589,plain,(
% 0.22/0.55    $false | (~spl10_4 | spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f588,f581])).
% 0.22/0.55  fof(f581,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f489,f465])).
% 0.22/0.55  fof(f465,plain,(
% 0.22/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f210,f245])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl10_4),
% 0.22/0.55    inference(backward_demodulation,[],[f56,f116])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f489,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(resolution,[],[f464,f88])).
% 0.22/0.55  fof(f464,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f211,f245])).
% 0.22/0.55  % (19137)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  fof(f211,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl10_4),
% 0.22/0.55    inference(backward_demodulation,[],[f57,f116])).
% 0.22/0.55  fof(f588,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_4 | spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f587,f245])).
% 0.22/0.55  fof(f587,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl10_4 | spl10_9)),
% 0.22/0.55    inference(forward_demodulation,[],[f205,f116])).
% 0.22/0.55  fof(f205,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,sK1,sK3) | spl10_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f204])).
% 0.22/0.55  fof(f580,plain,(
% 0.22/0.55    ~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f579])).
% 0.22/0.55  fof(f579,plain,(
% 0.22/0.55    $false | (~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f578,f131])).
% 0.22/0.55  fof(f578,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f577,f55])).
% 0.22/0.55  fof(f577,plain,(
% 0.22/0.55    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f576,f196])).
% 0.22/0.55  fof(f576,plain,(
% 0.22/0.55    sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | spl10_8 | ~spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f575,f485])).
% 0.22/0.55  fof(f485,plain,(
% 0.22/0.55    ~r2_hidden(sK4(sK2,sK3),k1_xboole_0) | (spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f200,f245])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    ~r2_hidden(sK4(sK2,sK3),sK0) | spl10_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f199])).
% 0.22/0.55  fof(f575,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | ~spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f574])).
% 0.22/0.55  fof(f574,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4(sK2,sK3),k1_xboole_0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | ~spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(superposition,[],[f522,f461])).
% 0.22/0.55  fof(f461,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(sK3) | (~spl10_4 | ~spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f460,f454])).
% 0.22/0.55  fof(f454,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_4 | ~spl10_9 | ~spl10_11)),
% 0.22/0.55    inference(backward_demodulation,[],[f351,f245])).
% 0.22/0.55  fof(f351,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl10_4 | ~spl10_9)),
% 0.22/0.55    inference(forward_demodulation,[],[f206,f116])).
% 0.22/0.55  fof(f460,plain,(
% 0.22/0.55    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f217,f245])).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl10_4),
% 0.22/0.55    inference(backward_demodulation,[],[f132,f116])).
% 0.22/0.55  fof(f522,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 != k1_relat_1(X1) | r2_hidden(sK4(sK2,X1),k1_xboole_0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl10_3 | ~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f521,f92])).
% 0.22/0.55  % (19163)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  fof(f521,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 != k1_relat_1(X1) | r2_hidden(sK4(sK2,X1),k1_xboole_0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | (~spl10_3 | ~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f518,f52])).
% 0.22/0.55  fof(f518,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 != k1_relat_1(X1) | r2_hidden(sK4(sK2,X1),k1_xboole_0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl10_3 | ~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(superposition,[],[f61,f456])).
% 0.22/0.55  fof(f456,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(sK2) | (~spl10_3 | ~spl10_4 | ~spl10_11)),
% 0.22/0.55    inference(backward_demodulation,[],[f451,f245])).
% 0.22/0.55  fof(f451,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2) | (~spl10_3 | ~spl10_4)),
% 0.22/0.55    inference(forward_demodulation,[],[f450,f449])).
% 0.22/0.55  fof(f449,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) | (~spl10_3 | ~spl10_4)),
% 0.22/0.55    inference(forward_demodulation,[],[f112,f116])).
% 0.22/0.55  fof(f450,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl10_4),
% 0.22/0.55    inference(forward_demodulation,[],[f93,f116])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f448,plain,(
% 0.22/0.55    ~spl10_4 | spl10_7 | ~spl10_8 | ~spl10_10),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f447])).
% 0.22/0.55  fof(f447,plain,(
% 0.22/0.55    $false | (~spl10_4 | spl10_7 | ~spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f446,f60])).
% 0.22/0.55  fof(f446,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0) | (~spl10_4 | spl10_7 | ~spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(resolution,[],[f431,f63])).
% 0.22/0.55  fof(f431,plain,(
% 0.22/0.55    r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0) | (~spl10_4 | spl10_7 | ~spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(forward_demodulation,[],[f430,f241])).
% 0.22/0.55  fof(f241,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~spl10_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f239])).
% 0.22/0.55  fof(f239,plain,(
% 0.22/0.55    spl10_10 <=> k1_xboole_0 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.55  fof(f430,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | (~spl10_4 | spl10_7 | ~spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(forward_demodulation,[],[f201,f286])).
% 0.22/0.55  fof(f286,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f282,f261])).
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    k1_xboole_0 != sK3 | (spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f196,f241])).
% 0.22/0.55  fof(f282,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl10_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f273,f210])).
% 0.22/0.55  fof(f273,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl10_4),
% 0.22/0.55    inference(resolution,[],[f211,f86])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.22/0.55    inference(equality_resolution,[],[f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f429,plain,(
% 0.22/0.55    spl10_3 | ~spl10_4 | spl10_7 | ~spl10_10),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f428])).
% 0.22/0.55  fof(f428,plain,(
% 0.22/0.55    $false | (spl10_3 | ~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f427,f410])).
% 0.22/0.55  fof(f410,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f363,f306])).
% 0.22/0.55  fof(f306,plain,(
% 0.22/0.55    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f263,f286])).
% 0.22/0.55  fof(f263,plain,(
% 0.22/0.55    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl10_4 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f208,f241])).
% 0.22/0.55  fof(f363,plain,(
% 0.22/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(resolution,[],[f307,f88])).
% 0.22/0.55  fof(f307,plain,(
% 0.22/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f264,f286])).
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl10_4 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f209,f241])).
% 0.22/0.55  fof(f427,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl10_3 | ~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(forward_demodulation,[],[f426,f286])).
% 0.22/0.55  fof(f426,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (spl10_3 | ~spl10_4 | ~spl10_10)),
% 0.22/0.55    inference(forward_demodulation,[],[f425,f116])).
% 0.22/0.55  fof(f425,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,sK1,k1_xboole_0) | (spl10_3 | ~spl10_10)),
% 0.22/0.55    inference(forward_demodulation,[],[f111,f241])).
% 0.22/0.55  fof(f409,plain,(
% 0.22/0.55    ~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_10),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f408])).
% 0.22/0.55  fof(f408,plain,(
% 0.22/0.55    $false | (~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f407,f131])).
% 0.22/0.55  fof(f407,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f406,f55])).
% 0.22/0.55  fof(f406,plain,(
% 0.22/0.55    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f405,f261])).
% 0.22/0.55  fof(f405,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | spl10_7 | spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f404,f305])).
% 0.22/0.55  fof(f305,plain,(
% 0.22/0.55    ~r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0) | (~spl10_4 | spl10_7 | spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f262,f286])).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    ~r2_hidden(sK4(k1_xboole_0,sK3),sK0) | (spl10_8 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f200,f241])).
% 0.22/0.55  fof(f404,plain,(
% 0.22/0.55    r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0) | k1_xboole_0 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f403])).
% 0.22/0.55  fof(f403,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0) | k1_xboole_0 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | ~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(superposition,[],[f319,f348])).
% 0.22/0.55  fof(f348,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(sK3) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f293,f345])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f334,f290])).
% 0.22/0.55  fof(f290,plain,(
% 0.22/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f210,f286])).
% 0.22/0.55  fof(f334,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(resolution,[],[f291,f88])).
% 0.22/0.55  fof(f291,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f211,f286])).
% 0.22/0.55  fof(f293,plain,(
% 0.22/0.55    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f217,f286])).
% 0.22/0.55  % (19139)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  fof(f319,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 != k1_relat_1(X1) | r2_hidden(sK4(k1_xboole_0,X1),k1_xboole_0) | k1_xboole_0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl10_3 | ~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(forward_demodulation,[],[f311,f286])).
% 0.22/0.55  fof(f311,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 != k1_relat_1(X1) | k1_xboole_0 = X1 | r2_hidden(sK4(k1_xboole_0,X1),sK0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl10_3 | ~spl10_4 | spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f268,f286])).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = X1 | r2_hidden(sK4(k1_xboole_0,X1),sK0) | k1_relat_1(X1) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl10_3 | ~spl10_10)),
% 0.22/0.55    inference(forward_demodulation,[],[f257,f241])).
% 0.22/0.55  fof(f257,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK4(k1_xboole_0,X1),sK0) | k1_relat_1(X1) != sK0 | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl10_3 | ~spl10_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f157,f241])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl10_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f156,f92])).
% 0.22/0.55  % (19162)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | ~spl10_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f153,f52])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl10_3),
% 0.22/0.55    inference(superposition,[],[f61,f129])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2) | ~spl10_3),
% 0.22/0.55    inference(backward_demodulation,[],[f93,f112])).
% 0.22/0.55  fof(f246,plain,(
% 0.22/0.55    spl10_10 | spl10_11 | ~spl10_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f237,f114,f243,f239])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl10_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f228,f208])).
% 0.22/0.55  fof(f228,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl10_4),
% 0.22/0.55    inference(resolution,[],[f209,f86])).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    spl10_9 | spl10_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f138,f114,f204])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f134,f56])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.55    inference(resolution,[],[f57,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f202,plain,(
% 0.22/0.55    spl10_7 | spl10_8 | ~spl10_3 | spl10_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f193,f114,f110,f199,f195])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | (~spl10_3 | spl10_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f192,f131])).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl10_3 | spl10_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f191,f55])).
% 0.22/0.55  fof(f191,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | spl10_4)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f190])).
% 0.22/0.55  fof(f190,plain,(
% 0.22/0.55    sK0 != sK0 | r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_3 | spl10_4)),
% 0.22/0.55    inference(superposition,[],[f157,f140])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK3) | spl10_4),
% 0.22/0.55    inference(backward_demodulation,[],[f132,f139])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | spl10_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f138,f115])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    k1_xboole_0 != sK1 | spl10_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f114])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    ~spl10_5),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f127])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    $false | ~spl10_5),
% 0.22/0.55    inference(subsumption_resolution,[],[f121,f98])).
% 0.22/0.55  % (19164)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ~sP9(sK1,sK0)),
% 0.22/0.55    inference(resolution,[],[f54,f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP9(X1,X0)) )),
% 0.22/0.55    inference(general_splitting,[],[f83,f89_D])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP9(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f89_D])).
% 0.22/0.55  fof(f89_D,plain,(
% 0.22/0.55    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP9(X1,X0)) )),
% 0.22/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.55  % (19165)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    sP9(sK1,sK0) | ~spl10_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f119])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    spl10_5 <=> sP9(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    spl10_5 | spl10_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f97,f123,f119])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | sP9(sK1,sK0)),
% 0.22/0.55    inference(resolution,[],[f54,f89])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    spl10_3 | spl10_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f108,f114,f110])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f95,f53])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(resolution,[],[f54,f77])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (19144)------------------------------
% 0.22/0.55  % (19144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (19144)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (19144)Memory used [KB]: 11001
% 0.22/0.55  % (19144)Time elapsed: 0.107 s
% 0.22/0.55  % (19144)------------------------------
% 0.22/0.55  % (19144)------------------------------
% 0.22/0.55  % (19161)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (19156)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (19160)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (19154)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (19146)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (19145)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (19155)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (19157)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (19147)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (19149)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (19153)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.57  % (19135)Success in time 0.194 s
%------------------------------------------------------------------------------
