%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:27 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 753 expanded)
%              Number of leaves         :   33 ( 243 expanded)
%              Depth                    :   22
%              Number of atoms          :  652 (5735 expanded)
%              Number of equality atoms :  156 (1767 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f142,f148,f160,f166,f202,f254,f308,f413,f739,f1132])).

fof(f1132,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_15
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f1131])).

fof(f1131,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_15
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1130,f275])).

fof(f275,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f76,f169])).

fof(f169,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f69,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK3)
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f28,f60,f59])).

fof(f59,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK1 != k2_relset_1(sK0,sK1,sK3)
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X4] :
        ( sK1 != k2_relset_1(sK0,sK1,sK3)
        & k1_xboole_0 != sK2
        & v2_funct_1(X4)
        & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK3)
      & k1_xboole_0 != sK2
      & v2_funct_1(sK4)
      & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f76,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f1130,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f1129,f766])).

fof(f766,plain,
    ( sK1 = k10_relat_1(sK4,sK2)
    | ~ spl5_1
    | ~ spl5_15 ),
    inference(backward_demodulation,[],[f313,f253])).

fof(f253,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl5_15
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f313,plain,
    ( sK1 = k10_relat_1(sK4,k2_relat_1(sK4))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f210,f276])).

fof(f276,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f193,f204])).

fof(f204,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f203,f75])).

fof(f75,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f61])).

fof(f203,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f197,f71])).

fof(f71,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f197,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f72,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

fof(f193,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f72,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f210,plain,
    ( k1_relat_1(sK4) = k10_relat_1(sK4,k2_relat_1(sK4))
    | ~ spl5_1 ),
    inference(resolution,[],[f132,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f132,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_1
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1129,plain,
    ( k2_relat_1(sK3) = k10_relat_1(sK4,sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f1122,f977])).

fof(f977,plain,
    ( sK2 = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f475,f695])).

fof(f695,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f684,f553])).

fof(f553,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f73,f385])).

fof(f385,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f382,f67])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f382,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f205,f69])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f198,f70])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f72,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f73,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f61])).

fof(f684,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f558,f104])).

fof(f558,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f557,f67])).

fof(f557,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f556,f69])).

fof(f556,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f555,f70])).

fof(f555,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f554,f72])).

fof(f554,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f115,f385])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f475,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1 ),
    inference(resolution,[],[f208,f167])).

fof(f167,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f208,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(X1,sK4)) = k9_relat_1(sK4,k2_relat_1(X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f132,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f1122,plain,
    ( k2_relat_1(sK3) = k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(resolution,[],[f435,f218])).

fof(f218,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f217,f167])).

fof(f217,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f171,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f171,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f69,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

% (18232)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f435,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f434,f136])).

fof(f136,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_2
  <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f434,plain,
    ( ! [X0] :
        ( k10_relat_1(sK4,k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ r1_tarski(X0,sK1) )
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f433,f141])).

fof(f141,plain,
    ( ! [X1] : k10_relat_1(sK4,X1) = k9_relat_1(k2_funct_1(sK4),X1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_3
  <=> ! [X1] : k10_relat_1(sK4,X1) = k9_relat_1(k2_funct_1(sK4),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f433,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 )
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f432,f159])).

fof(f159,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_6
  <=> v1_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f432,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f428,f165])).

fof(f165,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl5_7
  <=> v1_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f428,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ v1_funct_1(k2_funct_1(sK4))
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_19 ),
    inference(superposition,[],[f95,f307])).

fof(f307,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl5_19
  <=> sK1 = k2_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f739,plain,
    ( ~ spl5_1
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f738])).

fof(f738,plain,
    ( $false
    | ~ spl5_1
    | spl5_14 ),
    inference(subsumption_resolution,[],[f737,f167])).

fof(f737,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_1
    | spl5_14 ),
    inference(subsumption_resolution,[],[f736,f132])).

fof(f736,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | spl5_14 ),
    inference(subsumption_resolution,[],[f731,f249])).

fof(f249,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK4))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl5_14
  <=> r1_tarski(sK2,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f731,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f81,f695])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f413,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_6
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_6
    | spl5_18 ),
    inference(subsumption_resolution,[],[f411,f303])).

fof(f303,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK1)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl5_18
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f411,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f410,f276])).

fof(f410,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f407,f132])).

fof(f407,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(superposition,[],[f88,f400])).

fof(f400,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k10_relat_1(sK4,k1_relat_1(k2_funct_1(sK4)))
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(superposition,[],[f213,f141])).

fof(f213,plain,
    ( k9_relat_1(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4))) = k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_6 ),
    inference(resolution,[],[f159,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f308,plain,
    ( ~ spl5_18
    | spl5_19
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f295,f157,f145,f131,f305,f301])).

fof(f145,plain,
    ( spl5_4
  <=> k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f295,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK4))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK1)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f293,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f293,plain,
    ( r1_tarski(sK1,k2_relat_1(k2_funct_1(sK4)))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f292,f78])).

fof(f78,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f292,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(k2_funct_1(sK4)))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f291,f132])).

fof(f291,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(k2_funct_1(sK4)))
    | ~ v1_relat_1(sK4)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f290,f159])).

fof(f290,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(k2_funct_1(sK4)))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_4 ),
    inference(superposition,[],[f81,f289])).

fof(f289,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1)
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f147,f276])).

fof(f147,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f254,plain,
    ( ~ spl5_14
    | spl5_15
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f245,f131,f251,f247])).

fof(f245,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ spl5_1 ),
    inference(resolution,[],[f222,f99])).

fof(f222,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f221,f132])).

fof(f221,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f196,f91])).

fof(f196,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f72,f106])).

fof(f202,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f192,f133])).

fof(f133,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f192,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f72,f102])).

fof(f166,plain,
    ( ~ spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f161,f163,f131])).

fof(f161,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f128,f70])).

fof(f128,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f74,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f74,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f160,plain,
    ( ~ spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f155,f157,f131])).

fof(f155,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f127,f70])).

fof(f127,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f74,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f148,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f143,f145,f131])).

fof(f143,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f125,f70])).

fof(f125,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f74,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f142,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f138,f140,f131])).

fof(f138,plain,(
    ! [X1] :
      ( k10_relat_1(sK4,X1) = k9_relat_1(k2_funct_1(sK4),X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f124,f70])).

fof(f124,plain,(
    ! [X1] :
      ( k10_relat_1(sK4,X1) = k9_relat_1(k2_funct_1(sK4),X1)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f74,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f137,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f129,f135,f131])).

fof(f129,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f123,f70])).

fof(f123,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f74,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:59:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (18208)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (18210)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.18/0.51  % (18231)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.18/0.51  % (18215)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.18/0.51  % (18228)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.18/0.52  % (18223)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.18/0.52  % (18226)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.18/0.52  % (18227)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.18/0.52  % (18214)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.18/0.52  % (18217)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.18/0.52  % (18213)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.18/0.52  % (18216)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.18/0.53  % (18218)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.18/0.53  % (18221)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.31/0.53  % (18211)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.31/0.53  % (18230)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.31/0.54  % (18209)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.31/0.54  % (18229)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.31/0.54  % (18206)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.31/0.54  % (18222)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.31/0.54  % (18233)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.31/0.55  % (18219)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.31/0.55  % (18208)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.55  % (18224)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.31/0.56  % (18220)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.31/0.56  % SZS output start Proof for theBenchmark
% 1.31/0.56  fof(f1133,plain,(
% 1.31/0.56    $false),
% 1.31/0.56    inference(avatar_sat_refutation,[],[f137,f142,f148,f160,f166,f202,f254,f308,f413,f739,f1132])).
% 1.31/0.56  fof(f1132,plain,(
% 1.31/0.56    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_15 | ~spl5_19),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f1131])).
% 1.31/0.56  fof(f1131,plain,(
% 1.31/0.56    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_15 | ~spl5_19)),
% 1.31/0.56    inference(subsumption_resolution,[],[f1130,f275])).
% 1.31/0.56  fof(f275,plain,(
% 1.31/0.56    sK1 != k2_relat_1(sK3)),
% 1.31/0.56    inference(superposition,[],[f76,f169])).
% 1.31/0.56  fof(f169,plain,(
% 1.31/0.56    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.31/0.56    inference(resolution,[],[f69,f104])).
% 1.31/0.56  fof(f104,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f51])).
% 1.31/0.56  fof(f51,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(ennf_transformation,[],[f21])).
% 1.31/0.56  fof(f21,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.31/0.56  fof(f69,plain,(
% 1.31/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f61,plain,(
% 1.31/0.56    (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f28,f60,f59])).
% 1.31/0.56  fof(f59,plain,(
% 1.31/0.56    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f60,plain,(
% 1.31/0.56    ? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f28,plain,(
% 1.31/0.56    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.31/0.56    inference(flattening,[],[f27])).
% 1.31/0.56  fof(f27,plain,(
% 1.31/0.56    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.31/0.56    inference(ennf_transformation,[],[f26])).
% 1.31/0.56  fof(f26,negated_conjecture,(
% 1.31/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.31/0.56    inference(negated_conjecture,[],[f25])).
% 1.31/0.56  fof(f25,conjecture,(
% 1.31/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 1.31/0.56  fof(f76,plain,(
% 1.31/0.56    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f1130,plain,(
% 1.31/0.56    sK1 = k2_relat_1(sK3) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_15 | ~spl5_19)),
% 1.31/0.56    inference(forward_demodulation,[],[f1129,f766])).
% 1.31/0.56  fof(f766,plain,(
% 1.31/0.56    sK1 = k10_relat_1(sK4,sK2) | (~spl5_1 | ~spl5_15)),
% 1.31/0.56    inference(backward_demodulation,[],[f313,f253])).
% 1.31/0.56  fof(f253,plain,(
% 1.31/0.56    sK2 = k2_relat_1(sK4) | ~spl5_15),
% 1.31/0.56    inference(avatar_component_clause,[],[f251])).
% 1.31/0.56  fof(f251,plain,(
% 1.31/0.56    spl5_15 <=> sK2 = k2_relat_1(sK4)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.31/0.56  fof(f313,plain,(
% 1.31/0.56    sK1 = k10_relat_1(sK4,k2_relat_1(sK4)) | ~spl5_1),
% 1.31/0.56    inference(forward_demodulation,[],[f210,f276])).
% 1.31/0.56  fof(f276,plain,(
% 1.31/0.56    sK1 = k1_relat_1(sK4)),
% 1.31/0.56    inference(forward_demodulation,[],[f193,f204])).
% 1.31/0.56  fof(f204,plain,(
% 1.31/0.56    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.31/0.56    inference(subsumption_resolution,[],[f203,f75])).
% 1.31/0.56  fof(f75,plain,(
% 1.31/0.56    k1_xboole_0 != sK2),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f203,plain,(
% 1.31/0.56    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.31/0.56    inference(subsumption_resolution,[],[f197,f71])).
% 1.31/0.56  fof(f71,plain,(
% 1.31/0.56    v1_funct_2(sK4,sK1,sK2)),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f197,plain,(
% 1.31/0.56    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.31/0.56    inference(resolution,[],[f72,f107])).
% 1.31/0.56  fof(f107,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f66])).
% 1.31/0.56  fof(f66,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(nnf_transformation,[],[f54])).
% 1.31/0.56  fof(f54,plain,(
% 1.31/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(flattening,[],[f53])).
% 1.31/0.56  fof(f53,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(ennf_transformation,[],[f22])).
% 1.31/0.56  fof(f22,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.31/0.56  fof(f72,plain,(
% 1.31/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f193,plain,(
% 1.31/0.56    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 1.31/0.56    inference(resolution,[],[f72,f103])).
% 1.31/0.56  fof(f103,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f50])).
% 1.31/0.56  fof(f50,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(ennf_transformation,[],[f20])).
% 1.31/0.56  fof(f20,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.31/0.56  fof(f210,plain,(
% 1.31/0.56    k1_relat_1(sK4) = k10_relat_1(sK4,k2_relat_1(sK4)) | ~spl5_1),
% 1.31/0.56    inference(resolution,[],[f132,f79])).
% 1.31/0.56  fof(f79,plain,(
% 1.31/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f29])).
% 1.31/0.56  fof(f29,plain,(
% 1.31/0.56    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.31/0.56    inference(ennf_transformation,[],[f8])).
% 1.31/0.56  fof(f8,axiom,(
% 1.31/0.56    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.31/0.56  fof(f132,plain,(
% 1.31/0.56    v1_relat_1(sK4) | ~spl5_1),
% 1.31/0.56    inference(avatar_component_clause,[],[f131])).
% 1.31/0.56  fof(f131,plain,(
% 1.31/0.56    spl5_1 <=> v1_relat_1(sK4)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.31/0.56  fof(f1129,plain,(
% 1.31/0.56    k2_relat_1(sK3) = k10_relat_1(sK4,sK2) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_19)),
% 1.31/0.56    inference(forward_demodulation,[],[f1122,f977])).
% 1.31/0.56  fof(f977,plain,(
% 1.31/0.56    sK2 = k9_relat_1(sK4,k2_relat_1(sK3)) | ~spl5_1),
% 1.31/0.56    inference(forward_demodulation,[],[f475,f695])).
% 1.31/0.56  fof(f695,plain,(
% 1.31/0.56    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.31/0.56    inference(forward_demodulation,[],[f684,f553])).
% 1.31/0.56  fof(f553,plain,(
% 1.31/0.56    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.31/0.56    inference(backward_demodulation,[],[f73,f385])).
% 1.31/0.56  fof(f385,plain,(
% 1.31/0.56    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.31/0.56    inference(subsumption_resolution,[],[f382,f67])).
% 1.31/0.56  fof(f67,plain,(
% 1.31/0.56    v1_funct_1(sK3)),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f382,plain,(
% 1.31/0.56    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 1.31/0.56    inference(resolution,[],[f205,f69])).
% 1.31/0.56  fof(f205,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(X2)) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f198,f70])).
% 1.31/0.56  fof(f70,plain,(
% 1.31/0.56    v1_funct_1(sK4)),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f198,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.31/0.56    inference(resolution,[],[f72,f113])).
% 1.31/0.56  fof(f113,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f56])).
% 1.31/0.56  fof(f56,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.31/0.56    inference(flattening,[],[f55])).
% 1.31/0.56  fof(f55,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.31/0.56    inference(ennf_transformation,[],[f24])).
% 1.31/0.56  fof(f24,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.31/0.56  fof(f73,plain,(
% 1.31/0.56    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f684,plain,(
% 1.31/0.56    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.31/0.56    inference(resolution,[],[f558,f104])).
% 1.31/0.56  fof(f558,plain,(
% 1.31/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.31/0.56    inference(subsumption_resolution,[],[f557,f67])).
% 1.31/0.56  fof(f557,plain,(
% 1.31/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3)),
% 1.31/0.56    inference(subsumption_resolution,[],[f556,f69])).
% 1.31/0.56  fof(f556,plain,(
% 1.31/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.31/0.56    inference(subsumption_resolution,[],[f555,f70])).
% 1.31/0.56  fof(f555,plain,(
% 1.31/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.31/0.56    inference(subsumption_resolution,[],[f554,f72])).
% 1.31/0.56  fof(f554,plain,(
% 1.31/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.31/0.56    inference(superposition,[],[f115,f385])).
% 1.31/0.56  fof(f115,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f58])).
% 1.31/0.56  fof(f58,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.31/0.56    inference(flattening,[],[f57])).
% 1.31/0.56  fof(f57,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.31/0.56    inference(ennf_transformation,[],[f23])).
% 1.31/0.56  fof(f23,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.31/0.56  fof(f475,plain,(
% 1.31/0.56    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) | ~spl5_1),
% 1.31/0.56    inference(resolution,[],[f208,f167])).
% 1.31/0.56  fof(f167,plain,(
% 1.31/0.56    v1_relat_1(sK3)),
% 1.31/0.56    inference(resolution,[],[f69,f102])).
% 1.31/0.56  fof(f102,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f49])).
% 1.31/0.56  fof(f49,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(ennf_transformation,[],[f18])).
% 1.31/0.56  fof(f18,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.31/0.56  fof(f208,plain,(
% 1.31/0.56    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,sK4)) = k9_relat_1(sK4,k2_relat_1(X1))) ) | ~spl5_1),
% 1.31/0.56    inference(resolution,[],[f132,f82])).
% 1.31/0.56  fof(f82,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f32])).
% 1.31/0.56  fof(f32,plain,(
% 1.31/0.56    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.31/0.56    inference(ennf_transformation,[],[f6])).
% 1.31/0.56  fof(f6,axiom,(
% 1.31/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.31/0.56  fof(f1122,plain,(
% 1.31/0.56    k2_relat_1(sK3) = k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) | (~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_19)),
% 1.31/0.56    inference(resolution,[],[f435,f218])).
% 1.31/0.56  fof(f218,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.31/0.56    inference(subsumption_resolution,[],[f217,f167])).
% 1.31/0.56  fof(f217,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.31/0.56    inference(resolution,[],[f171,f91])).
% 1.31/0.56  fof(f91,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f62])).
% 1.31/0.56  fof(f62,plain,(
% 1.31/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.31/0.56    inference(nnf_transformation,[],[f40])).
% 1.31/0.56  fof(f40,plain,(
% 1.31/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.56    inference(ennf_transformation,[],[f3])).
% 1.31/0.56  fof(f3,axiom,(
% 1.31/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.31/0.56  fof(f171,plain,(
% 1.31/0.56    v5_relat_1(sK3,sK1)),
% 1.31/0.56    inference(resolution,[],[f69,f106])).
% 1.31/0.56  fof(f106,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f52])).
% 1.31/0.56  % (18232)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.31/0.56  fof(f52,plain,(
% 1.31/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(ennf_transformation,[],[f19])).
% 1.31/0.56  fof(f19,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.31/0.56  fof(f435,plain,(
% 1.31/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0) ) | (~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_19)),
% 1.31/0.56    inference(forward_demodulation,[],[f434,f136])).
% 1.31/0.56  fof(f136,plain,(
% 1.31/0.56    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)) ) | ~spl5_2),
% 1.31/0.56    inference(avatar_component_clause,[],[f135])).
% 1.31/0.56  fof(f135,plain,(
% 1.31/0.56    spl5_2 <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.31/0.56  fof(f434,plain,(
% 1.31/0.56    ( ! [X0] : (k10_relat_1(sK4,k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~r1_tarski(X0,sK1)) ) | (~spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_19)),
% 1.31/0.56    inference(forward_demodulation,[],[f433,f141])).
% 1.31/0.56  fof(f141,plain,(
% 1.31/0.56    ( ! [X1] : (k10_relat_1(sK4,X1) = k9_relat_1(k2_funct_1(sK4),X1)) ) | ~spl5_3),
% 1.31/0.56    inference(avatar_component_clause,[],[f140])).
% 1.31/0.56  fof(f140,plain,(
% 1.31/0.56    spl5_3 <=> ! [X1] : k10_relat_1(sK4,X1) = k9_relat_1(k2_funct_1(sK4),X1)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.31/0.56  fof(f433,plain,(
% 1.31/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0) ) | (~spl5_6 | ~spl5_7 | ~spl5_19)),
% 1.31/0.56    inference(subsumption_resolution,[],[f432,f159])).
% 1.31/0.56  fof(f159,plain,(
% 1.31/0.56    v1_relat_1(k2_funct_1(sK4)) | ~spl5_6),
% 1.31/0.56    inference(avatar_component_clause,[],[f157])).
% 1.31/0.56  fof(f157,plain,(
% 1.31/0.56    spl5_6 <=> v1_relat_1(k2_funct_1(sK4))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.31/0.56  fof(f432,plain,(
% 1.31/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~v1_relat_1(k2_funct_1(sK4))) ) | (~spl5_7 | ~spl5_19)),
% 1.31/0.56    inference(subsumption_resolution,[],[f428,f165])).
% 1.31/0.56  fof(f165,plain,(
% 1.31/0.56    v1_funct_1(k2_funct_1(sK4)) | ~spl5_7),
% 1.31/0.56    inference(avatar_component_clause,[],[f163])).
% 1.31/0.56  fof(f163,plain,(
% 1.31/0.56    spl5_7 <=> v1_funct_1(k2_funct_1(sK4))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.31/0.56  fof(f428,plain,(
% 1.31/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))) ) | ~spl5_19),
% 1.31/0.56    inference(superposition,[],[f95,f307])).
% 1.31/0.56  fof(f307,plain,(
% 1.31/0.56    sK1 = k2_relat_1(k2_funct_1(sK4)) | ~spl5_19),
% 1.31/0.56    inference(avatar_component_clause,[],[f305])).
% 1.31/0.56  fof(f305,plain,(
% 1.31/0.56    spl5_19 <=> sK1 = k2_relat_1(k2_funct_1(sK4))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.31/0.56  fof(f95,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f46])).
% 1.31/0.56  fof(f46,plain,(
% 1.31/0.56    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.56    inference(flattening,[],[f45])).
% 1.31/0.56  fof(f45,plain,(
% 1.31/0.56    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.56    inference(ennf_transformation,[],[f14])).
% 1.31/0.56  fof(f14,axiom,(
% 1.31/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.31/0.56  fof(f739,plain,(
% 1.31/0.56    ~spl5_1 | spl5_14),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f738])).
% 1.31/0.56  fof(f738,plain,(
% 1.31/0.56    $false | (~spl5_1 | spl5_14)),
% 1.31/0.56    inference(subsumption_resolution,[],[f737,f167])).
% 1.31/0.56  fof(f737,plain,(
% 1.31/0.56    ~v1_relat_1(sK3) | (~spl5_1 | spl5_14)),
% 1.31/0.56    inference(subsumption_resolution,[],[f736,f132])).
% 1.31/0.56  fof(f736,plain,(
% 1.31/0.56    ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | spl5_14),
% 1.31/0.56    inference(subsumption_resolution,[],[f731,f249])).
% 1.31/0.56  fof(f249,plain,(
% 1.31/0.56    ~r1_tarski(sK2,k2_relat_1(sK4)) | spl5_14),
% 1.31/0.56    inference(avatar_component_clause,[],[f247])).
% 1.31/0.56  fof(f247,plain,(
% 1.31/0.56    spl5_14 <=> r1_tarski(sK2,k2_relat_1(sK4))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.31/0.56  fof(f731,plain,(
% 1.31/0.56    r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 1.31/0.56    inference(superposition,[],[f81,f695])).
% 1.31/0.56  fof(f81,plain,(
% 1.31/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f31])).
% 1.31/0.56  fof(f31,plain,(
% 1.31/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.31/0.56    inference(ennf_transformation,[],[f10])).
% 1.31/0.56  fof(f10,axiom,(
% 1.31/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.31/0.56  fof(f413,plain,(
% 1.31/0.56    ~spl5_1 | ~spl5_3 | ~spl5_6 | spl5_18),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f412])).
% 1.31/0.56  fof(f412,plain,(
% 1.31/0.56    $false | (~spl5_1 | ~spl5_3 | ~spl5_6 | spl5_18)),
% 1.31/0.56    inference(subsumption_resolution,[],[f411,f303])).
% 1.31/0.56  fof(f303,plain,(
% 1.31/0.56    ~r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK1) | spl5_18),
% 1.31/0.56    inference(avatar_component_clause,[],[f301])).
% 1.31/0.56  fof(f301,plain,(
% 1.31/0.56    spl5_18 <=> r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK1)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.31/0.56  fof(f411,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK1) | (~spl5_1 | ~spl5_3 | ~spl5_6)),
% 1.31/0.56    inference(forward_demodulation,[],[f410,f276])).
% 1.31/0.56  fof(f410,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)) | (~spl5_1 | ~spl5_3 | ~spl5_6)),
% 1.31/0.56    inference(subsumption_resolution,[],[f407,f132])).
% 1.31/0.56  fof(f407,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_3 | ~spl5_6)),
% 1.31/0.56    inference(superposition,[],[f88,f400])).
% 1.31/0.56  fof(f400,plain,(
% 1.31/0.56    k2_relat_1(k2_funct_1(sK4)) = k10_relat_1(sK4,k1_relat_1(k2_funct_1(sK4))) | (~spl5_3 | ~spl5_6)),
% 1.31/0.56    inference(superposition,[],[f213,f141])).
% 1.31/0.56  fof(f213,plain,(
% 1.31/0.56    k9_relat_1(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4))) = k2_relat_1(k2_funct_1(sK4)) | ~spl5_6),
% 1.31/0.56    inference(resolution,[],[f159,f80])).
% 1.31/0.56  fof(f80,plain,(
% 1.31/0.56    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f30])).
% 1.31/0.56  fof(f30,plain,(
% 1.31/0.56    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.56    inference(ennf_transformation,[],[f4])).
% 1.31/0.56  fof(f4,axiom,(
% 1.31/0.56    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.31/0.56  fof(f88,plain,(
% 1.31/0.56    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f37])).
% 1.31/0.56  fof(f37,plain,(
% 1.31/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.31/0.56    inference(ennf_transformation,[],[f7])).
% 1.31/0.56  fof(f7,axiom,(
% 1.31/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.31/0.56  fof(f308,plain,(
% 1.31/0.56    ~spl5_18 | spl5_19 | ~spl5_1 | ~spl5_4 | ~spl5_6),
% 1.31/0.56    inference(avatar_split_clause,[],[f295,f157,f145,f131,f305,f301])).
% 1.31/0.56  fof(f145,plain,(
% 1.31/0.56    spl5_4 <=> k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.31/0.56  fof(f295,plain,(
% 1.31/0.56    sK1 = k2_relat_1(k2_funct_1(sK4)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK1) | (~spl5_1 | ~spl5_4 | ~spl5_6)),
% 1.31/0.56    inference(resolution,[],[f293,f99])).
% 1.31/0.56  fof(f99,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f64])).
% 1.31/0.56  fof(f64,plain,(
% 1.31/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.56    inference(flattening,[],[f63])).
% 1.31/0.56  fof(f63,plain,(
% 1.31/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.56    inference(nnf_transformation,[],[f1])).
% 1.31/0.56  fof(f1,axiom,(
% 1.31/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.56  fof(f293,plain,(
% 1.31/0.56    r1_tarski(sK1,k2_relat_1(k2_funct_1(sK4))) | (~spl5_1 | ~spl5_4 | ~spl5_6)),
% 1.31/0.56    inference(forward_demodulation,[],[f292,f78])).
% 1.31/0.56  fof(f78,plain,(
% 1.31/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f11])).
% 1.31/0.56  fof(f11,axiom,(
% 1.31/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.31/0.56  fof(f292,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(k2_funct_1(sK4))) | (~spl5_1 | ~spl5_4 | ~spl5_6)),
% 1.31/0.56    inference(subsumption_resolution,[],[f291,f132])).
% 1.31/0.56  fof(f291,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(k2_funct_1(sK4))) | ~v1_relat_1(sK4) | (~spl5_4 | ~spl5_6)),
% 1.31/0.56    inference(subsumption_resolution,[],[f290,f159])).
% 1.31/0.56  fof(f290,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(k2_funct_1(sK4))) | ~v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4) | ~spl5_4),
% 1.31/0.56    inference(superposition,[],[f81,f289])).
% 1.31/0.56  fof(f289,plain,(
% 1.31/0.56    k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1) | ~spl5_4),
% 1.31/0.56    inference(forward_demodulation,[],[f147,f276])).
% 1.31/0.56  fof(f147,plain,(
% 1.31/0.56    k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) | ~spl5_4),
% 1.31/0.56    inference(avatar_component_clause,[],[f145])).
% 1.31/0.56  fof(f254,plain,(
% 1.31/0.56    ~spl5_14 | spl5_15 | ~spl5_1),
% 1.31/0.56    inference(avatar_split_clause,[],[f245,f131,f251,f247])).
% 1.31/0.56  fof(f245,plain,(
% 1.31/0.56    sK2 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~spl5_1),
% 1.31/0.56    inference(resolution,[],[f222,f99])).
% 1.31/0.56  fof(f222,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(sK4),sK2) | ~spl5_1),
% 1.31/0.56    inference(subsumption_resolution,[],[f221,f132])).
% 1.31/0.56  fof(f221,plain,(
% 1.31/0.56    r1_tarski(k2_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 1.31/0.56    inference(resolution,[],[f196,f91])).
% 1.31/0.56  fof(f196,plain,(
% 1.31/0.56    v5_relat_1(sK4,sK2)),
% 1.31/0.56    inference(resolution,[],[f72,f106])).
% 1.31/0.56  fof(f202,plain,(
% 1.31/0.56    spl5_1),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f201])).
% 1.31/0.56  fof(f201,plain,(
% 1.31/0.56    $false | spl5_1),
% 1.31/0.56    inference(subsumption_resolution,[],[f192,f133])).
% 1.31/0.56  fof(f133,plain,(
% 1.31/0.56    ~v1_relat_1(sK4) | spl5_1),
% 1.31/0.56    inference(avatar_component_clause,[],[f131])).
% 1.31/0.56  fof(f192,plain,(
% 1.31/0.56    v1_relat_1(sK4)),
% 1.31/0.56    inference(resolution,[],[f72,f102])).
% 1.31/0.56  fof(f166,plain,(
% 1.31/0.56    ~spl5_1 | spl5_7),
% 1.31/0.56    inference(avatar_split_clause,[],[f161,f163,f131])).
% 1.31/0.56  fof(f161,plain,(
% 1.31/0.56    v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.31/0.56    inference(subsumption_resolution,[],[f128,f70])).
% 1.31/0.56  fof(f128,plain,(
% 1.31/0.56    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.31/0.56    inference(resolution,[],[f74,f84])).
% 1.31/0.56  fof(f84,plain,(
% 1.31/0.56    ( ! [X0] : (~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f34])).
% 1.31/0.56  fof(f34,plain,(
% 1.31/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.56    inference(flattening,[],[f33])).
% 1.31/0.56  fof(f33,plain,(
% 1.31/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.56    inference(ennf_transformation,[],[f13])).
% 1.31/0.56  fof(f13,axiom,(
% 1.31/0.56    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.31/0.56  fof(f74,plain,(
% 1.31/0.56    v2_funct_1(sK4)),
% 1.31/0.56    inference(cnf_transformation,[],[f61])).
% 1.31/0.56  fof(f160,plain,(
% 1.31/0.56    ~spl5_1 | spl5_6),
% 1.31/0.56    inference(avatar_split_clause,[],[f155,f157,f131])).
% 1.31/0.56  fof(f155,plain,(
% 1.31/0.56    v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.31/0.56    inference(subsumption_resolution,[],[f127,f70])).
% 1.31/0.56  fof(f127,plain,(
% 1.31/0.56    v1_relat_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.31/0.56    inference(resolution,[],[f74,f83])).
% 1.31/0.56  fof(f83,plain,(
% 1.31/0.56    ( ! [X0] : (~v2_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f34])).
% 1.31/0.56  fof(f148,plain,(
% 1.31/0.56    ~spl5_1 | spl5_4),
% 1.31/0.56    inference(avatar_split_clause,[],[f143,f145,f131])).
% 1.31/0.56  fof(f143,plain,(
% 1.31/0.56    k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.31/0.56    inference(subsumption_resolution,[],[f125,f70])).
% 1.31/0.56  fof(f125,plain,(
% 1.31/0.56    k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.31/0.56    inference(resolution,[],[f74,f86])).
% 1.31/0.56  fof(f86,plain,(
% 1.31/0.56    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f36])).
% 1.31/0.56  fof(f36,plain,(
% 1.31/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.56    inference(flattening,[],[f35])).
% 1.31/0.56  fof(f35,plain,(
% 1.31/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.56    inference(ennf_transformation,[],[f17])).
% 1.31/0.56  fof(f17,axiom,(
% 1.31/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.31/0.56  fof(f142,plain,(
% 1.31/0.56    ~spl5_1 | spl5_3),
% 1.31/0.56    inference(avatar_split_clause,[],[f138,f140,f131])).
% 1.31/0.56  fof(f138,plain,(
% 1.31/0.56    ( ! [X1] : (k10_relat_1(sK4,X1) = k9_relat_1(k2_funct_1(sK4),X1) | ~v1_relat_1(sK4)) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f124,f70])).
% 1.31/0.56  fof(f124,plain,(
% 1.31/0.56    ( ! [X1] : (k10_relat_1(sK4,X1) = k9_relat_1(k2_funct_1(sK4),X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.31/0.56    inference(resolution,[],[f74,f93])).
% 1.31/0.56  fof(f93,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f42])).
% 1.31/0.56  fof(f42,plain,(
% 1.31/0.56    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.56    inference(flattening,[],[f41])).
% 1.31/0.56  fof(f41,plain,(
% 1.31/0.56    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.56    inference(ennf_transformation,[],[f16])).
% 1.31/0.56  fof(f16,axiom,(
% 1.31/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.31/0.56  fof(f137,plain,(
% 1.31/0.56    ~spl5_1 | spl5_2),
% 1.31/0.56    inference(avatar_split_clause,[],[f129,f135,f131])).
% 1.31/0.56  fof(f129,plain,(
% 1.31/0.56    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_relat_1(sK4)) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f123,f70])).
% 1.31/0.56  fof(f123,plain,(
% 1.31/0.56    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.31/0.56    inference(resolution,[],[f74,f94])).
% 1.31/0.56  fof(f94,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f44])).
% 1.31/0.56  fof(f44,plain,(
% 1.31/0.56    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.56    inference(flattening,[],[f43])).
% 1.31/0.56  fof(f43,plain,(
% 1.31/0.56    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.56    inference(ennf_transformation,[],[f15])).
% 1.31/0.56  fof(f15,axiom,(
% 1.31/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.31/0.56  % SZS output end Proof for theBenchmark
% 1.31/0.56  % (18208)------------------------------
% 1.31/0.56  % (18208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (18208)Termination reason: Refutation
% 1.31/0.56  
% 1.31/0.56  % (18208)Memory used [KB]: 11257
% 1.31/0.56  % (18208)Time elapsed: 0.134 s
% 1.31/0.56  % (18208)------------------------------
% 1.31/0.56  % (18208)------------------------------
% 1.31/0.56  % (18202)Success in time 0.2 s
%------------------------------------------------------------------------------
