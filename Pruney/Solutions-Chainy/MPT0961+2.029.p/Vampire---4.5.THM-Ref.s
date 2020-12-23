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
% DateTime   : Thu Dec  3 13:00:15 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 192 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  370 ( 730 expanded)
%              Number of equality atoms :  103 ( 197 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f508,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f115,f137,f147,f170,f424,f436,f507])).

fof(f507,plain,
    ( spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f505,f211])).

fof(f211,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_10 ),
    inference(resolution,[],[f189,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f189,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f177,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f177,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f93,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_10
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f93,plain,(
    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f505,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f504,f74])).

fof(f504,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f497,f423])).

fof(f423,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl5_22
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f497,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(superposition,[],[f477,f50])).

% (25633)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f477,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f476,f211])).

fof(f476,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f465,f74])).

fof(f465,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(resolution,[],[f445,f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f445,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f178,f423])).

fof(f178,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl5_2
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f87,f146])).

fof(f87,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f436,plain,(
    ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f425,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f425,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_funct_1(sK0,sK4(k1_relat_1(sK0))))
    | ~ spl5_21 ),
    inference(resolution,[],[f418,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f418,plain,
    ( r2_hidden(k1_funct_1(sK0,sK4(k1_relat_1(sK0))),k1_xboole_0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl5_21
  <=> r2_hidden(k1_funct_1(sK0,sK4(k1_relat_1(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f424,plain,
    ( spl5_22
    | spl5_21
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f404,f144,f113,f416,f421])).

fof(f113,plain,
    ( spl5_7
  <=> ! [X4] :
        ( r2_hidden(k1_funct_1(sK0,X4),k2_relat_1(sK0))
        | ~ r2_hidden(X4,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f404,plain,
    ( r2_hidden(k1_funct_1(sK0,sK4(k1_relat_1(sK0))),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(resolution,[],[f379,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f379,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X4),k1_xboole_0) )
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f114,f146])).

fof(f114,plain,
    ( ! [X4] :
        ( r2_hidden(k1_funct_1(sK0,X4),k2_relat_1(sK0))
        | ~ r2_hidden(X4,k1_relat_1(sK0)) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f170,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f165,f93])).

fof(f165,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl5_3 ),
    inference(resolution,[],[f91,f52])).

fof(f91,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f147,plain,
    ( ~ spl5_3
    | spl5_10
    | spl5_2 ),
    inference(avatar_split_clause,[],[f142,f85,f144,f89])).

fof(f142,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f138,f50])).

fof(f138,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl5_2 ),
    inference(resolution,[],[f87,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f137,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f42,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,
    ( ~ v1_funct_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f115,plain,
    ( ~ spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f97,f113,f81])).

fof(f97,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK0,X4),k2_relat_1(sK0))
      | ~ r2_hidden(X4,k1_relat_1(sK0))
      | ~ v1_funct_1(sK0) ) ),
    inference(resolution,[],[f41,f77])).

fof(f77,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

% (25623)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK1(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f92,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f43,f89,f85,f81])).

fof(f43,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:00:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.43  % (25622)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.43  % (25639)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.18/0.43  % (25639)Refutation not found, incomplete strategy% (25639)------------------------------
% 0.18/0.43  % (25639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.43  % (25639)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.43  
% 0.18/0.43  % (25639)Memory used [KB]: 10618
% 0.18/0.43  % (25639)Time elapsed: 0.056 s
% 0.18/0.43  % (25639)------------------------------
% 0.18/0.43  % (25639)------------------------------
% 0.18/0.45  % (25630)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.46  % (25626)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.18/0.46  % (25632)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.47  % (25620)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.18/0.47  % (25638)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.47  % (25624)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.48  % (25628)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.18/0.48  % (25619)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.48  % (25638)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % (25621)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.48  % (25631)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.49  % (25637)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.18/0.49  % (25634)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.18/0.49  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f508,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(avatar_sat_refutation,[],[f92,f115,f137,f147,f170,f424,f436,f507])).
% 0.18/0.49  fof(f507,plain,(
% 0.18/0.49    spl5_2 | ~spl5_10 | ~spl5_22),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f506])).
% 0.18/0.49  fof(f506,plain,(
% 0.18/0.49    $false | (spl5_2 | ~spl5_10 | ~spl5_22)),
% 0.18/0.49    inference(subsumption_resolution,[],[f505,f211])).
% 0.18/0.49  fof(f211,plain,(
% 0.18/0.49    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~spl5_10),
% 0.18/0.49    inference(resolution,[],[f189,f52])).
% 0.18/0.49  fof(f52,plain,(
% 0.18/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f30])).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.18/0.49    inference(nnf_transformation,[],[f6])).
% 0.18/0.49  fof(f6,axiom,(
% 0.18/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.18/0.49  fof(f189,plain,(
% 0.18/0.49    r1_tarski(sK0,k1_xboole_0) | ~spl5_10),
% 0.18/0.49    inference(forward_demodulation,[],[f177,f74])).
% 0.18/0.49  fof(f74,plain,(
% 0.18/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.18/0.49    inference(equality_resolution,[],[f56])).
% 0.18/0.49  fof(f56,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.18/0.49    inference(cnf_transformation,[],[f32])).
% 0.18/0.49  fof(f32,plain,(
% 0.18/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.49    inference(flattening,[],[f31])).
% 0.18/0.49  fof(f31,plain,(
% 0.18/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.49    inference(nnf_transformation,[],[f5])).
% 0.18/0.49  fof(f5,axiom,(
% 0.18/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.49  fof(f177,plain,(
% 0.18/0.49    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) | ~spl5_10),
% 0.18/0.49    inference(backward_demodulation,[],[f93,f146])).
% 0.18/0.49  fof(f146,plain,(
% 0.18/0.49    k1_xboole_0 = k2_relat_1(sK0) | ~spl5_10),
% 0.18/0.49    inference(avatar_component_clause,[],[f144])).
% 0.18/0.49  fof(f144,plain,(
% 0.18/0.49    spl5_10 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.18/0.49  fof(f93,plain,(
% 0.18/0.49    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.18/0.49    inference(resolution,[],[f41,f57])).
% 0.18/0.49  fof(f57,plain,(
% 0.18/0.49    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f7])).
% 0.18/0.49  fof(f7,axiom,(
% 0.18/0.49    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.18/0.49  fof(f41,plain,(
% 0.18/0.49    v1_relat_1(sK0)),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f27])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.18/0.49    inference(flattening,[],[f15])).
% 0.18/0.49  fof(f15,plain,(
% 0.18/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f14])).
% 0.18/0.49  fof(f14,negated_conjecture,(
% 0.18/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.18/0.49    inference(negated_conjecture,[],[f13])).
% 0.18/0.49  fof(f13,conjecture,(
% 0.18/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.18/0.49  fof(f505,plain,(
% 0.18/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | (spl5_2 | ~spl5_10 | ~spl5_22)),
% 0.18/0.49    inference(forward_demodulation,[],[f504,f74])).
% 0.18/0.49  fof(f504,plain,(
% 0.18/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_10 | ~spl5_22)),
% 0.18/0.49    inference(subsumption_resolution,[],[f497,f423])).
% 0.18/0.49  fof(f423,plain,(
% 0.18/0.49    k1_xboole_0 = k1_relat_1(sK0) | ~spl5_22),
% 0.18/0.49    inference(avatar_component_clause,[],[f421])).
% 0.18/0.49  fof(f421,plain,(
% 0.18/0.49    spl5_22 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.18/0.49  fof(f497,plain,(
% 0.18/0.49    k1_xboole_0 != k1_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_10 | ~spl5_22)),
% 0.18/0.49    inference(superposition,[],[f477,f50])).
% 0.18/0.49  % (25633)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.49  fof(f50,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f19])).
% 0.18/0.49  fof(f19,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(ennf_transformation,[],[f11])).
% 0.18/0.49  fof(f11,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.49  fof(f477,plain,(
% 0.18/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) | (spl5_2 | ~spl5_10 | ~spl5_22)),
% 0.18/0.49    inference(subsumption_resolution,[],[f476,f211])).
% 0.18/0.49  fof(f476,plain,(
% 0.18/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) | (spl5_2 | ~spl5_10 | ~spl5_22)),
% 0.18/0.49    inference(forward_demodulation,[],[f465,f74])).
% 0.18/0.49  fof(f465,plain,(
% 0.18/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_10 | ~spl5_22)),
% 0.18/0.49    inference(resolution,[],[f445,f72])).
% 0.18/0.49  fof(f72,plain,(
% 0.18/0.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.18/0.49    inference(equality_resolution,[],[f47])).
% 0.18/0.49  fof(f47,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f29])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(nnf_transformation,[],[f18])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(flattening,[],[f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(ennf_transformation,[],[f12])).
% 0.18/0.49  fof(f12,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.18/0.49  fof(f445,plain,(
% 0.18/0.49    ~v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_10 | ~spl5_22)),
% 0.18/0.49    inference(backward_demodulation,[],[f178,f423])).
% 0.18/0.49  fof(f178,plain,(
% 0.18/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl5_2 | ~spl5_10)),
% 0.18/0.49    inference(backward_demodulation,[],[f87,f146])).
% 0.18/0.49  fof(f87,plain,(
% 0.18/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl5_2),
% 0.18/0.49    inference(avatar_component_clause,[],[f85])).
% 0.18/0.49  fof(f85,plain,(
% 0.18/0.49    spl5_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.18/0.49  fof(f436,plain,(
% 0.18/0.49    ~spl5_21),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f435])).
% 0.18/0.49  fof(f435,plain,(
% 0.18/0.49    $false | ~spl5_21),
% 0.18/0.49    inference(subsumption_resolution,[],[f425,f66])).
% 0.18/0.49  fof(f66,plain,(
% 0.18/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f4])).
% 0.18/0.49  fof(f4,axiom,(
% 0.18/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.49  fof(f425,plain,(
% 0.18/0.49    ~r1_tarski(k1_xboole_0,k1_funct_1(sK0,sK4(k1_relat_1(sK0)))) | ~spl5_21),
% 0.18/0.49    inference(resolution,[],[f418,f68])).
% 0.18/0.49  fof(f68,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f26])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.18/0.49    inference(ennf_transformation,[],[f9])).
% 0.18/0.49  fof(f9,axiom,(
% 0.18/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.18/0.49  fof(f418,plain,(
% 0.18/0.49    r2_hidden(k1_funct_1(sK0,sK4(k1_relat_1(sK0))),k1_xboole_0) | ~spl5_21),
% 0.18/0.49    inference(avatar_component_clause,[],[f416])).
% 0.18/0.49  fof(f416,plain,(
% 0.18/0.49    spl5_21 <=> r2_hidden(k1_funct_1(sK0,sK4(k1_relat_1(sK0))),k1_xboole_0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.18/0.49  fof(f424,plain,(
% 0.18/0.49    spl5_22 | spl5_21 | ~spl5_7 | ~spl5_10),
% 0.18/0.49    inference(avatar_split_clause,[],[f404,f144,f113,f416,f421])).
% 0.18/0.49  fof(f113,plain,(
% 0.18/0.49    spl5_7 <=> ! [X4] : (r2_hidden(k1_funct_1(sK0,X4),k2_relat_1(sK0)) | ~r2_hidden(X4,k1_relat_1(sK0)))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.18/0.49  fof(f404,plain,(
% 0.18/0.49    r2_hidden(k1_funct_1(sK0,sK4(k1_relat_1(sK0))),k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK0) | (~spl5_7 | ~spl5_10)),
% 0.18/0.49    inference(resolution,[],[f379,f64])).
% 0.18/0.49  fof(f64,plain,(
% 0.18/0.49    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f40])).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f39])).
% 0.18/0.49  fof(f39,plain,(
% 0.18/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.18/0.49    inference(ennf_transformation,[],[f3])).
% 0.18/0.49  fof(f3,axiom,(
% 0.18/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.18/0.49  fof(f379,plain,(
% 0.18/0.49    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X4),k1_xboole_0)) ) | (~spl5_7 | ~spl5_10)),
% 0.18/0.49    inference(forward_demodulation,[],[f114,f146])).
% 0.18/0.49  fof(f114,plain,(
% 0.18/0.49    ( ! [X4] : (r2_hidden(k1_funct_1(sK0,X4),k2_relat_1(sK0)) | ~r2_hidden(X4,k1_relat_1(sK0))) ) | ~spl5_7),
% 0.18/0.49    inference(avatar_component_clause,[],[f113])).
% 0.18/0.49  fof(f170,plain,(
% 0.18/0.49    spl5_3),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f169])).
% 0.18/0.49  fof(f169,plain,(
% 0.18/0.49    $false | spl5_3),
% 0.18/0.49    inference(subsumption_resolution,[],[f165,f93])).
% 0.18/0.49  fof(f165,plain,(
% 0.18/0.49    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl5_3),
% 0.18/0.49    inference(resolution,[],[f91,f52])).
% 0.18/0.49  fof(f91,plain,(
% 0.18/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl5_3),
% 0.18/0.49    inference(avatar_component_clause,[],[f89])).
% 0.18/0.49  fof(f89,plain,(
% 0.18/0.49    spl5_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.18/0.49  fof(f147,plain,(
% 0.18/0.49    ~spl5_3 | spl5_10 | spl5_2),
% 0.18/0.49    inference(avatar_split_clause,[],[f142,f85,f144,f89])).
% 0.18/0.49  fof(f142,plain,(
% 0.18/0.49    k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl5_2),
% 0.18/0.49    inference(subsumption_resolution,[],[f138,f50])).
% 0.18/0.49  fof(f138,plain,(
% 0.18/0.49    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl5_2),
% 0.18/0.49    inference(resolution,[],[f87,f46])).
% 0.18/0.49  fof(f46,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f29])).
% 0.18/0.49  fof(f137,plain,(
% 0.18/0.49    spl5_1),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f136])).
% 0.18/0.49  fof(f136,plain,(
% 0.18/0.49    $false | spl5_1),
% 0.18/0.49    inference(subsumption_resolution,[],[f83,f42])).
% 0.18/0.49  fof(f42,plain,(
% 0.18/0.49    v1_funct_1(sK0)),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f83,plain,(
% 0.18/0.49    ~v1_funct_1(sK0) | spl5_1),
% 0.18/0.49    inference(avatar_component_clause,[],[f81])).
% 0.18/0.49  fof(f81,plain,(
% 0.18/0.49    spl5_1 <=> v1_funct_1(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.18/0.49  fof(f115,plain,(
% 0.18/0.49    ~spl5_1 | spl5_7),
% 0.18/0.49    inference(avatar_split_clause,[],[f97,f113,f81])).
% 0.18/0.49  fof(f97,plain,(
% 0.18/0.49    ( ! [X4] : (r2_hidden(k1_funct_1(sK0,X4),k2_relat_1(sK0)) | ~r2_hidden(X4,k1_relat_1(sK0)) | ~v1_funct_1(sK0)) )),
% 0.18/0.49    inference(resolution,[],[f41,f77])).
% 0.18/0.49  fof(f77,plain,(
% 0.18/0.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.49    inference(equality_resolution,[],[f76])).
% 0.18/0.49  fof(f76,plain,(
% 0.18/0.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.49    inference(equality_resolution,[],[f60])).
% 0.18/0.49  fof(f60,plain,(
% 0.18/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f38])).
% 0.18/0.49  fof(f38,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 0.18/0.49  % (25623)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f36,plain,(
% 0.18/0.49    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f37,plain,(
% 0.18/0.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f34,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(rectify,[],[f33])).
% 0.18/0.49  fof(f33,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(nnf_transformation,[],[f23])).
% 0.18/0.49  fof(f23,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(flattening,[],[f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f8])).
% 0.18/0.49  fof(f8,axiom,(
% 0.18/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.18/0.49  fof(f92,plain,(
% 0.18/0.49    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.18/0.49    inference(avatar_split_clause,[],[f43,f89,f85,f81])).
% 0.18/0.49  fof(f43,plain,(
% 0.18/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (25638)------------------------------
% 0.18/0.49  % (25638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (25638)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (25638)Memory used [KB]: 6268
% 0.18/0.49  % (25638)Time elapsed: 0.080 s
% 0.18/0.49  % (25638)------------------------------
% 0.18/0.49  % (25638)------------------------------
% 0.18/0.49  % (25621)Refutation not found, incomplete strategy% (25621)------------------------------
% 0.18/0.49  % (25621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (25621)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (25621)Memory used [KB]: 10618
% 0.18/0.49  % (25621)Time elapsed: 0.092 s
% 0.18/0.49  % (25621)------------------------------
% 0.18/0.49  % (25621)------------------------------
% 0.18/0.50  % (25615)Success in time 0.153 s
%------------------------------------------------------------------------------
