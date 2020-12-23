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
% DateTime   : Thu Dec  3 13:07:33 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 702 expanded)
%              Number of leaves         :   29 ( 210 expanded)
%              Depth                    :   20
%              Number of atoms          :  546 (4119 expanded)
%              Number of equality atoms :  119 ( 465 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f130,f137,f177,f183,f262,f296,f298,f312,f444,f463])).

fof(f463,plain,
    ( spl5_3
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f192,f459])).

fof(f459,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f102,f152])).

fof(f152,plain,(
    ! [X2] : k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2) ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(f143,plain,(
    ! [X2] :
      ( k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f51,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f192,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_10
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f444,plain,
    ( spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f442,f317])).

fof(f317,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f301,f316])).

fof(f316,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f175,f197])).

fof(f197,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f175,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl5_9
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f301,plain,
    ( m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f167,f197])).

fof(f167,plain,(
    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f156,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f156,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(backward_demodulation,[],[f53,f144])).

fof(f144,plain,(
    ! [X3] : k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3) ),
    inference(resolution,[],[f51,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f53,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f442,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f441,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f441,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f432,f398])).

fof(f398,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f358,f389])).

fof(f389,plain,
    ( k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f388,f317])).

fof(f388,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f379,f89])).

fof(f379,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | spl5_2
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(resolution,[],[f357,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f357,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl5_2
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f303,f355])).

fof(f355,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f345,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f345,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ r1_tarski(k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(resolution,[],[f314,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f314,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f308,f89])).

fof(f308,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0))
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f274,f197])).

fof(f274,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl5_10 ),
    inference(resolution,[],[f192,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f303,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl5_2
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f184,f197])).

fof(f184,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(forward_demodulation,[],[f98,f152])).

fof(f98,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f358,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f305,f355])).

fof(f305,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f200,f197])).

fof(f200,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl5_12
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f432,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(resolution,[],[f397,f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f397,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f357,f389])).

fof(f312,plain,
    ( spl5_8
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f302,f79])).

fof(f302,plain,
    ( ~ r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1))
    | spl5_8
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f171,f197])).

fof(f171,plain,
    ( ~ r1_tarski(sK2,k9_relat_1(sK4,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl5_8
  <=> r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f298,plain,
    ( spl5_11
    | ~ spl5_12
    | spl5_2
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f297,f191,f96,f199,f195])).

fof(f297,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f271,f184])).

fof(f271,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | ~ spl5_10 ),
    inference(resolution,[],[f192,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f296,plain,
    ( ~ spl5_7
    | ~ spl5_10
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_10
    | spl5_12 ),
    inference(subsumption_resolution,[],[f294,f52])).

fof(f52,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f294,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_7
    | ~ spl5_10
    | spl5_12 ),
    inference(forward_demodulation,[],[f293,f157])).

fof(f157,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f147,f129])).

fof(f129,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_7
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f147,plain,(
    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f293,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ spl5_10
    | spl5_12 ),
    inference(subsumption_resolution,[],[f292,f148])).

fof(f148,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f51,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f292,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_10
    | spl5_12 ),
    inference(trivial_inequality_removal,[],[f291])).

fof(f291,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_10
    | spl5_12 ),
    inference(superposition,[],[f290,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f290,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_10
    | spl5_12 ),
    inference(subsumption_resolution,[],[f287,f192])).

fof(f287,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_12 ),
    inference(superposition,[],[f201,f75])).

fof(f201,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f199])).

fof(f262,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f260,f156])).

fof(f260,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | spl5_10 ),
    inference(forward_demodulation,[],[f259,f159])).

fof(f159,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK4,X2)) = k9_relat_1(sK4,X2) ),
    inference(resolution,[],[f148,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f259,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f258,f160])).

fof(f160,plain,(
    ! [X3] : v1_relat_1(k7_relat_1(sK4,X3)) ),
    inference(resolution,[],[f148,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f258,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_10 ),
    inference(subsumption_resolution,[],[f256,f161])).

fof(f161,plain,(
    ! [X4] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X4)),X4) ),
    inference(resolution,[],[f148,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f256,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_10 ),
    inference(resolution,[],[f193,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f193,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f183,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f155,f153])).

fof(f153,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl5_1 ),
    inference(backward_demodulation,[],[f94,f152])).

fof(f94,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f155,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(backward_demodulation,[],[f150,f152])).

fof(f150,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) ),
    inference(subsumption_resolution,[],[f141,f49])).

fof(f141,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f51,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f177,plain,
    ( ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f166,f173,f169])).

fof(f166,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    inference(resolution,[],[f156,f63])).

fof(f137,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f132,f70])).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f132,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f48,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f48,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f130,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f121,f127,f123])).

fof(f121,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f120,f51])).

fof(f120,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(resolution,[],[f50,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f50,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f54,f100,f96,f92])).

fof(f54,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (6247)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.47  % (6241)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (6243)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (6250)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (6263)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (6254)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (6240)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (6257)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (6242)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (6237)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (6246)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (6239)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (6249)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (6251)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (6238)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (6244)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (6248)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (6256)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (6260)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (6252)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (6259)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (6261)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (6255)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.55  % (6262)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.49/0.56  % (6245)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.49/0.57  % (6253)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.65/0.58  % (6248)Refutation found. Thanks to Tanya!
% 1.65/0.58  % SZS status Theorem for theBenchmark
% 1.65/0.58  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f464,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(avatar_sat_refutation,[],[f103,f130,f137,f177,f183,f262,f296,f298,f312,f444,f463])).
% 1.65/0.58  fof(f463,plain,(
% 1.65/0.58    spl5_3 | ~spl5_10),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f462])).
% 1.65/0.58  fof(f462,plain,(
% 1.65/0.58    $false | (spl5_3 | ~spl5_10)),
% 1.65/0.58    inference(subsumption_resolution,[],[f192,f459])).
% 1.65/0.58  fof(f459,plain,(
% 1.65/0.58    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 1.65/0.58    inference(forward_demodulation,[],[f102,f152])).
% 1.65/0.58  fof(f152,plain,(
% 1.65/0.58    ( ! [X2] : (k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2)) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f143,f49])).
% 1.65/0.58  fof(f49,plain,(
% 1.65/0.58    v1_funct_1(sK4)),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f41,plain,(
% 1.65/0.58    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 1.65/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f40,f39])).
% 1.65/0.58  fof(f39,plain,(
% 1.65/0.58    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f40,plain,(
% 1.65/0.58    ? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f22,plain,(
% 1.65/0.58    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.65/0.58    inference(flattening,[],[f21])).
% 1.65/0.58  fof(f21,plain,(
% 1.65/0.58    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.65/0.58    inference(ennf_transformation,[],[f20])).
% 1.65/0.58  fof(f20,negated_conjecture,(
% 1.65/0.58    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.65/0.58    inference(negated_conjecture,[],[f19])).
% 1.65/0.58  fof(f19,conjecture,(
% 1.65/0.58    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 1.65/0.58  fof(f143,plain,(
% 1.65/0.58    ( ! [X2] : (k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2) | ~v1_funct_1(sK4)) )),
% 1.65/0.58    inference(resolution,[],[f51,f57])).
% 1.65/0.58  fof(f57,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f26,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.65/0.58    inference(flattening,[],[f25])).
% 1.65/0.58  fof(f25,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.65/0.58    inference(ennf_transformation,[],[f18])).
% 1.65/0.58  fof(f18,axiom,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.65/0.58  fof(f51,plain,(
% 1.65/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f102,plain,(
% 1.65/0.58    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 1.65/0.58    inference(avatar_component_clause,[],[f100])).
% 1.65/0.58  fof(f100,plain,(
% 1.65/0.58    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.65/0.58  fof(f192,plain,(
% 1.65/0.58    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_10),
% 1.65/0.58    inference(avatar_component_clause,[],[f191])).
% 1.65/0.58  fof(f191,plain,(
% 1.65/0.58    spl5_10 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.65/0.58  fof(f444,plain,(
% 1.65/0.58    spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f443])).
% 1.65/0.58  fof(f443,plain,(
% 1.65/0.58    $false | (spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.65/0.58    inference(subsumption_resolution,[],[f442,f317])).
% 1.65/0.58  fof(f317,plain,(
% 1.65/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl5_9 | ~spl5_11)),
% 1.65/0.58    inference(backward_demodulation,[],[f301,f316])).
% 1.65/0.58  fof(f316,plain,(
% 1.65/0.58    k1_xboole_0 = k9_relat_1(sK4,sK1) | (~spl5_9 | ~spl5_11)),
% 1.65/0.58    inference(forward_demodulation,[],[f175,f197])).
% 1.65/0.58  fof(f197,plain,(
% 1.65/0.58    k1_xboole_0 = sK2 | ~spl5_11),
% 1.65/0.58    inference(avatar_component_clause,[],[f195])).
% 1.65/0.58  fof(f195,plain,(
% 1.65/0.58    spl5_11 <=> k1_xboole_0 = sK2),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.65/0.58  fof(f175,plain,(
% 1.65/0.58    sK2 = k9_relat_1(sK4,sK1) | ~spl5_9),
% 1.65/0.58    inference(avatar_component_clause,[],[f173])).
% 1.65/0.58  fof(f173,plain,(
% 1.65/0.58    spl5_9 <=> sK2 = k9_relat_1(sK4,sK1)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.65/0.58  fof(f301,plain,(
% 1.65/0.58    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) | ~spl5_11),
% 1.65/0.58    inference(backward_demodulation,[],[f167,f197])).
% 1.65/0.58  fof(f167,plain,(
% 1.65/0.58    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2))),
% 1.65/0.58    inference(resolution,[],[f156,f60])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f42])).
% 1.65/0.58  fof(f42,plain,(
% 1.65/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.65/0.58    inference(nnf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.65/0.58  fof(f156,plain,(
% 1.65/0.58    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.65/0.58    inference(backward_demodulation,[],[f53,f144])).
% 1.65/0.58  fof(f144,plain,(
% 1.65/0.58    ( ! [X3] : (k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3)) )),
% 1.65/0.58    inference(resolution,[],[f51,f58])).
% 1.65/0.58  fof(f58,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f27])).
% 1.65/0.58  fof(f27,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f14])).
% 1.65/0.58  fof(f14,axiom,(
% 1.65/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.65/0.58  fof(f53,plain,(
% 1.65/0.58    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f442,plain,(
% 1.65/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.65/0.58    inference(forward_demodulation,[],[f441,f89])).
% 1.65/0.58  fof(f89,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.65/0.58    inference(equality_resolution,[],[f78])).
% 1.65/0.58  fof(f78,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f47])).
% 1.65/0.58  fof(f47,plain,(
% 1.65/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.65/0.58    inference(flattening,[],[f46])).
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.65/0.58    inference(nnf_transformation,[],[f4])).
% 1.65/0.58  fof(f4,axiom,(
% 1.65/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.65/0.58  fof(f441,plain,(
% 1.65/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.65/0.58    inference(subsumption_resolution,[],[f432,f398])).
% 1.65/0.58  fof(f398,plain,(
% 1.65/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.65/0.58    inference(backward_demodulation,[],[f358,f389])).
% 1.65/0.58  fof(f389,plain,(
% 1.65/0.58    k1_xboole_0 = sK1 | (spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(subsumption_resolution,[],[f388,f317])).
% 1.65/0.58  fof(f388,plain,(
% 1.65/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | (spl5_2 | ~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(forward_demodulation,[],[f379,f89])).
% 1.65/0.58  fof(f379,plain,(
% 1.65/0.58    k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (spl5_2 | ~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(resolution,[],[f357,f85])).
% 1.65/0.58  fof(f85,plain,(
% 1.65/0.58    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.65/0.58    inference(equality_resolution,[],[f84])).
% 1.65/0.58  fof(f84,plain,(
% 1.65/0.58    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(equality_resolution,[],[f69])).
% 1.65/0.58  fof(f69,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f45])).
% 1.65/0.58  fof(f45,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(nnf_transformation,[],[f29])).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(flattening,[],[f28])).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f16])).
% 1.65/0.58  fof(f16,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.65/0.58  fof(f357,plain,(
% 1.65/0.58    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (spl5_2 | ~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(backward_demodulation,[],[f303,f355])).
% 1.65/0.58  fof(f355,plain,(
% 1.65/0.58    k1_xboole_0 = k7_relat_1(sK4,sK1) | (~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(subsumption_resolution,[],[f345,f79])).
% 1.65/0.58  fof(f79,plain,(
% 1.65/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f3])).
% 1.65/0.58  fof(f3,axiom,(
% 1.65/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.65/0.58  fof(f345,plain,(
% 1.65/0.58    k1_xboole_0 = k7_relat_1(sK4,sK1) | ~r1_tarski(k1_xboole_0,k7_relat_1(sK4,sK1)) | (~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(resolution,[],[f314,f63])).
% 1.65/0.58  fof(f63,plain,(
% 1.65/0.58    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f44])).
% 1.65/0.58  fof(f44,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(flattening,[],[f43])).
% 1.65/0.58  fof(f43,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(nnf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.65/0.58  fof(f314,plain,(
% 1.65/0.58    r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(forward_demodulation,[],[f308,f89])).
% 1.65/0.58  fof(f308,plain,(
% 1.65/0.58    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0)) | (~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(backward_demodulation,[],[f274,f197])).
% 1.65/0.58  fof(f274,plain,(
% 1.65/0.58    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) | ~spl5_10),
% 1.65/0.58    inference(resolution,[],[f192,f59])).
% 1.65/0.58  fof(f59,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f42])).
% 1.65/0.58  fof(f303,plain,(
% 1.65/0.58    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (spl5_2 | ~spl5_11)),
% 1.65/0.58    inference(backward_demodulation,[],[f184,f197])).
% 1.65/0.58  fof(f184,plain,(
% 1.65/0.58    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_2),
% 1.65/0.58    inference(forward_demodulation,[],[f98,f152])).
% 1.65/0.58  fof(f98,plain,(
% 1.65/0.58    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_2),
% 1.65/0.58    inference(avatar_component_clause,[],[f96])).
% 1.65/0.58  fof(f96,plain,(
% 1.65/0.58    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.65/0.58  fof(f358,plain,(
% 1.65/0.58    sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0) | (~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.65/0.58    inference(backward_demodulation,[],[f305,f355])).
% 1.65/0.58  fof(f305,plain,(
% 1.65/0.58    sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1)) | (~spl5_11 | ~spl5_12)),
% 1.65/0.58    inference(backward_demodulation,[],[f200,f197])).
% 1.65/0.58  fof(f200,plain,(
% 1.65/0.58    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_12),
% 1.65/0.58    inference(avatar_component_clause,[],[f199])).
% 1.65/0.58  fof(f199,plain,(
% 1.65/0.58    spl5_12 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.65/0.58  fof(f432,plain,(
% 1.65/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(resolution,[],[f397,f87])).
% 1.65/0.58  fof(f87,plain,(
% 1.65/0.58    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.65/0.58    inference(equality_resolution,[],[f67])).
% 1.65/0.58  fof(f67,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f45])).
% 1.65/0.58  fof(f397,plain,(
% 1.65/0.58    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_11)),
% 1.65/0.58    inference(backward_demodulation,[],[f357,f389])).
% 1.65/0.58  fof(f312,plain,(
% 1.65/0.58    spl5_8 | ~spl5_11),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f311])).
% 1.65/0.58  fof(f311,plain,(
% 1.65/0.58    $false | (spl5_8 | ~spl5_11)),
% 1.65/0.58    inference(subsumption_resolution,[],[f302,f79])).
% 1.65/0.58  fof(f302,plain,(
% 1.65/0.58    ~r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) | (spl5_8 | ~spl5_11)),
% 1.65/0.58    inference(backward_demodulation,[],[f171,f197])).
% 1.65/0.58  fof(f171,plain,(
% 1.65/0.58    ~r1_tarski(sK2,k9_relat_1(sK4,sK1)) | spl5_8),
% 1.65/0.58    inference(avatar_component_clause,[],[f169])).
% 1.65/0.58  fof(f169,plain,(
% 1.65/0.58    spl5_8 <=> r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.65/0.58  fof(f298,plain,(
% 1.65/0.58    spl5_11 | ~spl5_12 | spl5_2 | ~spl5_10),
% 1.65/0.58    inference(avatar_split_clause,[],[f297,f191,f96,f199,f195])).
% 1.65/0.58  fof(f297,plain,(
% 1.65/0.58    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | (spl5_2 | ~spl5_10)),
% 1.65/0.58    inference(subsumption_resolution,[],[f271,f184])).
% 1.65/0.58  fof(f271,plain,(
% 1.65/0.58    v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | ~spl5_10),
% 1.65/0.58    inference(resolution,[],[f192,f66])).
% 1.65/0.58  fof(f66,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f45])).
% 1.65/0.58  fof(f296,plain,(
% 1.65/0.58    ~spl5_7 | ~spl5_10 | spl5_12),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f295])).
% 1.65/0.58  fof(f295,plain,(
% 1.65/0.58    $false | (~spl5_7 | ~spl5_10 | spl5_12)),
% 1.65/0.58    inference(subsumption_resolution,[],[f294,f52])).
% 1.65/0.58  fof(f52,plain,(
% 1.65/0.58    r1_tarski(sK1,sK0)),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f294,plain,(
% 1.65/0.58    ~r1_tarski(sK1,sK0) | (~spl5_7 | ~spl5_10 | spl5_12)),
% 1.65/0.58    inference(forward_demodulation,[],[f293,f157])).
% 1.65/0.58  fof(f157,plain,(
% 1.65/0.58    sK0 = k1_relat_1(sK4) | ~spl5_7),
% 1.65/0.58    inference(forward_demodulation,[],[f147,f129])).
% 1.65/0.58  fof(f129,plain,(
% 1.65/0.58    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl5_7),
% 1.65/0.58    inference(avatar_component_clause,[],[f127])).
% 1.65/0.58  fof(f127,plain,(
% 1.65/0.58    spl5_7 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.65/0.58  fof(f147,plain,(
% 1.65/0.58    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 1.65/0.58    inference(resolution,[],[f51,f75])).
% 1.65/0.58  fof(f75,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f35])).
% 1.65/0.58  fof(f35,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f13])).
% 1.65/0.58  fof(f13,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.65/0.58  fof(f293,plain,(
% 1.65/0.58    ~r1_tarski(sK1,k1_relat_1(sK4)) | (~spl5_10 | spl5_12)),
% 1.65/0.58    inference(subsumption_resolution,[],[f292,f148])).
% 1.65/0.58  fof(f148,plain,(
% 1.65/0.58    v1_relat_1(sK4)),
% 1.65/0.58    inference(resolution,[],[f51,f80])).
% 1.65/0.58  fof(f80,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f36])).
% 1.65/0.58  fof(f36,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f11])).
% 1.65/0.58  fof(f11,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.65/0.58  fof(f292,plain,(
% 1.65/0.58    ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_10 | spl5_12)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f291])).
% 1.65/0.58  fof(f291,plain,(
% 1.65/0.58    sK1 != sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_10 | spl5_12)),
% 1.65/0.58    inference(superposition,[],[f290,f71])).
% 1.65/0.58  fof(f71,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f31])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(flattening,[],[f30])).
% 1.65/0.58  fof(f30,plain,(
% 1.65/0.58    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f10])).
% 1.65/0.58  fof(f10,axiom,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.65/0.58  fof(f290,plain,(
% 1.65/0.58    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_10 | spl5_12)),
% 1.65/0.58    inference(subsumption_resolution,[],[f287,f192])).
% 1.65/0.58  fof(f287,plain,(
% 1.65/0.58    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_12),
% 1.65/0.58    inference(superposition,[],[f201,f75])).
% 1.65/0.58  fof(f201,plain,(
% 1.65/0.58    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | spl5_12),
% 1.65/0.58    inference(avatar_component_clause,[],[f199])).
% 1.65/0.58  fof(f262,plain,(
% 1.65/0.58    spl5_10),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f261])).
% 1.65/0.58  fof(f261,plain,(
% 1.65/0.58    $false | spl5_10),
% 1.65/0.58    inference(subsumption_resolution,[],[f260,f156])).
% 1.65/0.58  fof(f260,plain,(
% 1.65/0.58    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | spl5_10),
% 1.65/0.58    inference(forward_demodulation,[],[f259,f159])).
% 1.65/0.58  fof(f159,plain,(
% 1.65/0.58    ( ! [X2] : (k2_relat_1(k7_relat_1(sK4,X2)) = k9_relat_1(sK4,X2)) )),
% 1.65/0.58    inference(resolution,[],[f148,f74])).
% 1.65/0.58  fof(f74,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f34])).
% 1.65/0.58  fof(f34,plain,(
% 1.65/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f8])).
% 1.65/0.58  fof(f8,axiom,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.65/0.58  fof(f259,plain,(
% 1.65/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl5_10),
% 1.65/0.58    inference(subsumption_resolution,[],[f258,f160])).
% 1.65/0.58  fof(f160,plain,(
% 1.65/0.58    ( ! [X3] : (v1_relat_1(k7_relat_1(sK4,X3))) )),
% 1.65/0.58    inference(resolution,[],[f148,f73])).
% 1.65/0.58  fof(f73,plain,(
% 1.65/0.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f7])).
% 1.65/0.58  fof(f7,axiom,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.65/0.58  fof(f258,plain,(
% 1.65/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_10),
% 1.65/0.58    inference(subsumption_resolution,[],[f256,f161])).
% 1.65/0.58  fof(f161,plain,(
% 1.65/0.58    ( ! [X4] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X4)),X4)) )),
% 1.65/0.58    inference(resolution,[],[f148,f72])).
% 1.65/0.58  fof(f72,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f32])).
% 1.65/0.58  fof(f32,plain,(
% 1.65/0.58    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f9])).
% 1.65/0.58  fof(f9,axiom,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.65/0.58  fof(f256,plain,(
% 1.65/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_10),
% 1.65/0.58    inference(resolution,[],[f193,f81])).
% 1.65/0.58  fof(f81,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f38])).
% 1.65/0.58  fof(f38,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.65/0.58    inference(flattening,[],[f37])).
% 1.65/0.58  fof(f37,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.65/0.58    inference(ennf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.65/0.58  fof(f193,plain,(
% 1.65/0.58    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_10),
% 1.65/0.58    inference(avatar_component_clause,[],[f191])).
% 1.65/0.58  fof(f183,plain,(
% 1.65/0.58    spl5_1),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f179])).
% 1.65/0.58  fof(f179,plain,(
% 1.65/0.58    $false | spl5_1),
% 1.65/0.58    inference(resolution,[],[f155,f153])).
% 1.65/0.58  fof(f153,plain,(
% 1.65/0.58    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl5_1),
% 1.65/0.58    inference(backward_demodulation,[],[f94,f152])).
% 1.65/0.58  fof(f94,plain,(
% 1.65/0.58    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_1),
% 1.65/0.58    inference(avatar_component_clause,[],[f92])).
% 1.65/0.58  fof(f92,plain,(
% 1.65/0.58    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.65/0.58  fof(f155,plain,(
% 1.65/0.58    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 1.65/0.58    inference(backward_demodulation,[],[f150,f152])).
% 1.65/0.58  fof(f150,plain,(
% 1.65/0.58    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f141,f49])).
% 1.65/0.58  fof(f141,plain,(
% 1.65/0.58    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) | ~v1_funct_1(sK4)) )),
% 1.65/0.58    inference(resolution,[],[f51,f55])).
% 1.65/0.58  fof(f55,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f24,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.65/0.58    inference(flattening,[],[f23])).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.65/0.58    inference(ennf_transformation,[],[f17])).
% 1.65/0.58  fof(f17,axiom,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.65/0.58  fof(f177,plain,(
% 1.65/0.58    ~spl5_8 | spl5_9),
% 1.65/0.58    inference(avatar_split_clause,[],[f166,f173,f169])).
% 1.65/0.58  fof(f166,plain,(
% 1.65/0.58    sK2 = k9_relat_1(sK4,sK1) | ~r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 1.65/0.58    inference(resolution,[],[f156,f63])).
% 1.65/0.58  fof(f137,plain,(
% 1.65/0.58    ~spl5_6),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f136])).
% 1.65/0.58  fof(f136,plain,(
% 1.65/0.58    $false | ~spl5_6),
% 1.65/0.58    inference(subsumption_resolution,[],[f132,f70])).
% 1.65/0.58  fof(f70,plain,(
% 1.65/0.58    v1_xboole_0(k1_xboole_0)),
% 1.65/0.58    inference(cnf_transformation,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    v1_xboole_0(k1_xboole_0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.65/0.58  fof(f132,plain,(
% 1.65/0.58    ~v1_xboole_0(k1_xboole_0) | ~spl5_6),
% 1.65/0.58    inference(backward_demodulation,[],[f48,f125])).
% 1.65/0.58  fof(f125,plain,(
% 1.65/0.58    k1_xboole_0 = sK3 | ~spl5_6),
% 1.65/0.58    inference(avatar_component_clause,[],[f123])).
% 1.65/0.58  fof(f123,plain,(
% 1.65/0.58    spl5_6 <=> k1_xboole_0 = sK3),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.65/0.58  fof(f48,plain,(
% 1.65/0.58    ~v1_xboole_0(sK3)),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f130,plain,(
% 1.65/0.58    spl5_6 | spl5_7),
% 1.65/0.58    inference(avatar_split_clause,[],[f121,f127,f123])).
% 1.65/0.58  fof(f121,plain,(
% 1.65/0.58    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3),
% 1.65/0.58    inference(subsumption_resolution,[],[f120,f51])).
% 1.65/0.58  fof(f120,plain,(
% 1.65/0.58    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.65/0.58    inference(resolution,[],[f50,f64])).
% 1.65/0.58  fof(f64,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f45])).
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    v1_funct_2(sK4,sK0,sK3)),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f103,plain,(
% 1.65/0.58    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f54,f100,f96,f92])).
% 1.65/0.58  fof(f54,plain,(
% 1.65/0.58    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  % SZS output end Proof for theBenchmark
% 1.65/0.58  % (6248)------------------------------
% 1.65/0.58  % (6248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (6248)Termination reason: Refutation
% 1.65/0.58  
% 1.65/0.58  % (6248)Memory used [KB]: 10874
% 1.65/0.58  % (6248)Time elapsed: 0.157 s
% 1.65/0.58  % (6248)------------------------------
% 1.65/0.58  % (6248)------------------------------
% 1.65/0.58  % (6236)Success in time 0.224 s
%------------------------------------------------------------------------------
