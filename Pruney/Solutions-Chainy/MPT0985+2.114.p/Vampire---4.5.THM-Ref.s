%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 439 expanded)
%              Number of leaves         :   29 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  546 (2149 expanded)
%              Number of equality atoms :  129 ( 392 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f106,f125,f152,f290,f296,f301,f368,f499,f552,f554,f556,f558,f560,f561,f595,f631])).

fof(f631,plain,
    ( spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f629,f176])).

fof(f176,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f175,f66])).

fof(f66,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f175,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f174,f139])).

fof(f139,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f174,plain,
    ( ! [X0] : v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f173,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f134,f142])).

fof(f142,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f629,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f436,f142])).

fof(f436,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | spl3_2
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f89,f305])).

fof(f305,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl3_19
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f89,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f595,plain,
    ( spl3_3
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | spl3_3
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f593,f228])).

fof(f228,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl3_15
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f593,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f590,f74])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f590,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f570,f142])).

fof(f570,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f93,f305])).

fof(f93,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f561,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f510,f99,f109])).

fof(f109,plain,
    ( spl3_6
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f99,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f510,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f509,f100])).

fof(f100,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f509,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f505,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f33])).

fof(f33,plain,
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

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f505,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f560,plain,
    ( spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f559,f147,f141])).

fof(f147,plain,
    ( spl3_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f559,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f512,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f512,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f558,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f517,f99,f133])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) )
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f516,f100])).

fof(f516,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f514,f40])).

fof(f514,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f62,f118])).

fof(f118,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f117,f44])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f117,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f42,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f556,plain,
    ( spl3_9
    | ~ spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f555,f99,f141,f137])).

fof(f555,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f513,f100])).

fof(f513,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f65,f118])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f554,plain,
    ( spl3_19
    | ~ spl3_10
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f553,f284,f103,f141,f303])).

fof(f103,plain,
    ( spl3_5
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f284,plain,
    ( spl3_16
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f553,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f524,f285])).

fof(f285,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f284])).

fof(f524,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(superposition,[],[f64,f153])).

fof(f153,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f105,f118])).

fof(f105,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f552,plain,
    ( spl3_3
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | spl3_3
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f548,f93])).

fof(f548,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_18 ),
    inference(resolution,[],[f295,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f295,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl3_18
  <=> ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f499,plain,
    ( spl3_2
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f420,f288,f87])).

fof(f288,plain,
    ( spl3_17
  <=> ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f420,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_17 ),
    inference(resolution,[],[f289,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f288])).

fof(f368,plain,
    ( spl3_15
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f355,f141,f137,f226])).

fof(f355,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f326,f139])).

fof(f326,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f317,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f317,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f42,f142])).

fof(f301,plain,
    ( ~ spl3_4
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl3_4
    | spl3_16 ),
    inference(subsumption_resolution,[],[f299,f100])).

fof(f299,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f297,f40])).

fof(f297,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_16 ),
    inference(resolution,[],[f286,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f286,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f284])).

fof(f296,plain,
    ( ~ spl3_16
    | spl3_18
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f292,f147,f109,f103,f83,f294,f284])).

fof(f83,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f292,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(sK0,X1)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f291,f153])).

fof(f291,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f280,f84])).

fof(f84,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f280,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f63,f255])).

fof(f255,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f111,f252])).

fof(f252,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f116,f149])).

fof(f149,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f116,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f42,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f111,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f290,plain,
    ( ~ spl3_16
    | spl3_17
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f282,f147,f109,f103,f83,f288,f284])).

fof(f282,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f281,f153])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f279,f84])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f62,f255])).

fof(f152,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f151,f83,f99])).

fof(f151,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f114,f40])).

fof(f114,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f85,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f125,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f113,f42])).

fof(f113,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_4 ),
    inference(resolution,[],[f101,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f101,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f97,f103,f99])).

fof(f97,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f95,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f91,f87,f83])).

fof(f45,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:25:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (22201)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (22201)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (22217)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (22213)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (22209)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (22218)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (22206)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (22210)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (22214)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (22205)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (22198)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (22197)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (22207)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (22199)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (22212)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (22202)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (22208)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f663,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f94,f106,f125,f152,f290,f296,f301,f368,f499,f552,f554,f556,f558,f560,f561,f595,f631])).
% 0.22/0.53  fof(f631,plain,(
% 0.22/0.53    spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_19),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f630])).
% 0.22/0.53  fof(f630,plain,(
% 0.22/0.53    $false | (spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_19)),
% 0.22/0.53    inference(subsumption_resolution,[],[f629,f176])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl3_8 | ~spl3_9 | ~spl3_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f175,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) ) | (~spl3_8 | ~spl3_9 | ~spl3_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f174,f139])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | ~spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f137])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl3_9 <=> k1_xboole_0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | (~spl3_8 | ~spl3_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f173,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | (~spl3_8 | ~spl3_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f134,f142])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    spl3_10 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK1,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | ~spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f133])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    spl3_8 <=> ! [X0] : (~r1_tarski(sK1,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f629,plain,(
% 0.22/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl3_2 | ~spl3_10 | ~spl3_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f436,f142])).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    ~v1_funct_2(k1_xboole_0,sK1,sK0) | (spl3_2 | ~spl3_19)),
% 0.22/0.53    inference(backward_demodulation,[],[f89,f305])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    k1_xboole_0 = k2_funct_1(sK2) | ~spl3_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f303])).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    spl3_19 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f595,plain,(
% 0.22/0.53    spl3_3 | ~spl3_10 | ~spl3_15 | ~spl3_19),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f594])).
% 0.22/0.53  fof(f594,plain,(
% 0.22/0.53    $false | (spl3_3 | ~spl3_10 | ~spl3_15 | ~spl3_19)),
% 0.22/0.53    inference(subsumption_resolution,[],[f593,f228])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f226])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    spl3_15 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.53  fof(f593,plain,(
% 0.22/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl3_3 | ~spl3_10 | ~spl3_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f590,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f590,plain,(
% 0.22/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_10 | ~spl3_19)),
% 0.22/0.53    inference(backward_demodulation,[],[f570,f142])).
% 0.22/0.53  fof(f570,plain,(
% 0.22/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl3_3 | ~spl3_19)),
% 0.22/0.53    inference(backward_demodulation,[],[f93,f305])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f561,plain,(
% 0.22/0.53    spl3_6 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f510,f99,f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl3_6 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl3_4 <=> v1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f510,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.22/0.53    inference(subsumption_resolution,[],[f509,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f509,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f505,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    v1_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f16])).
% 0.22/0.53  fof(f16,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.53  fof(f505,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.53    inference(resolution,[],[f43,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    v2_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f560,plain,(
% 0.22/0.53    spl3_10 | spl3_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f559,f147,f141])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl3_11 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f559,plain,(
% 0.22/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.22/0.53    inference(subsumption_resolution,[],[f512,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f512,plain,(
% 0.22/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(resolution,[],[f41,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f558,plain,(
% 0.22/0.53    spl3_8 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f517,f99,f133])).
% 0.22/0.53  fof(f517,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK1,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | ~spl3_4),
% 0.22/0.53    inference(subsumption_resolution,[],[f516,f100])).
% 0.22/0.53  fof(f516,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK1,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f514,f40])).
% 0.22/0.53  fof(f514,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK1,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.53    inference(superposition,[],[f62,f118])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    sK1 = k2_relat_1(sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f117,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.53    inference(resolution,[],[f42,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.53  fof(f556,plain,(
% 0.22/0.53    spl3_9 | ~spl3_10 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f555,f99,f141,f137])).
% 0.22/0.53  fof(f555,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~spl3_4),
% 0.22/0.53    inference(subsumption_resolution,[],[f513,f100])).
% 0.22/0.53  fof(f513,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 0.22/0.53    inference(superposition,[],[f65,f118])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.53  fof(f554,plain,(
% 0.22/0.53    spl3_19 | ~spl3_10 | ~spl3_5 | ~spl3_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f553,f284,f103,f141,f303])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl3_5 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f284,plain,(
% 0.22/0.53    spl3_16 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.53  fof(f553,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2) | (~spl3_5 | ~spl3_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f524,f285])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    v1_relat_1(k2_funct_1(sK2)) | ~spl3_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f284])).
% 0.22/0.53  fof(f524,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.22/0.53    inference(superposition,[],[f64,f153])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.22/0.53    inference(forward_demodulation,[],[f105,f118])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f103])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f552,plain,(
% 0.22/0.53    spl3_3 | ~spl3_18),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f551])).
% 0.22/0.53  fof(f551,plain,(
% 0.22/0.53    $false | (spl3_3 | ~spl3_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f548,f93])).
% 0.22/0.53  fof(f548,plain,(
% 0.22/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_18),
% 0.22/0.53    inference(resolution,[],[f295,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_tarski(sK0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | ~spl3_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f294])).
% 0.22/0.53  fof(f294,plain,(
% 0.22/0.53    spl3_18 <=> ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(sK0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.53  fof(f499,plain,(
% 0.22/0.53    spl3_2 | ~spl3_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f420,f288,f87])).
% 0.22/0.53  fof(f288,plain,(
% 0.22/0.53    spl3_17 <=> ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(sK0,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.53  fof(f420,plain,(
% 0.22/0.53    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl3_17),
% 0.22/0.53    inference(resolution,[],[f289,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) ) | ~spl3_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f288])).
% 0.22/0.53  fof(f368,plain,(
% 0.22/0.53    spl3_15 | ~spl3_9 | ~spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f355,f141,f137,f226])).
% 0.22/0.53  fof(f355,plain,(
% 0.22/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_9 | ~spl3_10)),
% 0.22/0.53    inference(backward_demodulation,[],[f326,f139])).
% 0.22/0.53  fof(f326,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_10),
% 0.22/0.53    inference(forward_demodulation,[],[f317,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f317,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_10),
% 0.22/0.53    inference(backward_demodulation,[],[f42,f142])).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    ~spl3_4 | spl3_16),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f300])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    $false | (~spl3_4 | spl3_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f299,f100])).
% 0.22/0.53  fof(f299,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | spl3_16),
% 0.22/0.53    inference(subsumption_resolution,[],[f297,f40])).
% 0.22/0.53  fof(f297,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_16),
% 0.22/0.53    inference(resolution,[],[f286,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    ~v1_relat_1(k2_funct_1(sK2)) | spl3_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f284])).
% 0.22/0.53  fof(f296,plain,(
% 0.22/0.53    ~spl3_16 | spl3_18 | ~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f292,f147,f109,f103,f83,f294,f284])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f292,plain,(
% 0.22/0.53    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(sK0,X1) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f291,f153])).
% 0.22/0.53  fof(f291,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_tarski(sK0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_1 | ~spl3_6 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f280,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f83])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_tarski(sK0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_6 | ~spl3_11)),
% 0.22/0.53    inference(superposition,[],[f63,f255])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl3_6 | ~spl3_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f111,f252])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK2) | ~spl3_11),
% 0.22/0.53    inference(forward_demodulation,[],[f116,f149])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f147])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.53    inference(resolution,[],[f42,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f109])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f290,plain,(
% 0.22/0.53    ~spl3_16 | spl3_17 | ~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f282,f147,f109,f103,f83,f288,f284])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(sK0,X0) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f281,f153])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_1 | ~spl3_6 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f279,f84])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_6 | ~spl3_11)),
% 0.22/0.53    inference(superposition,[],[f62,f255])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ~spl3_4 | spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f151,f83,f99])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f114,f40])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.53    inference(resolution,[],[f85,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f83])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    $false | spl3_4),
% 0.22/0.53    inference(resolution,[],[f113,f42])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_4),
% 0.22/0.53    inference(resolution,[],[f101,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ~spl3_4 | spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f97,f103,f99])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f95,f40])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.53    inference(resolution,[],[f43,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f91,f87,f83])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (22201)------------------------------
% 0.22/0.53  % (22201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22201)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (22201)Memory used [KB]: 10874
% 0.22/0.53  % (22201)Time elapsed: 0.091 s
% 0.22/0.53  % (22201)------------------------------
% 0.22/0.53  % (22201)------------------------------
% 0.22/0.54  % (22194)Success in time 0.172 s
%------------------------------------------------------------------------------
