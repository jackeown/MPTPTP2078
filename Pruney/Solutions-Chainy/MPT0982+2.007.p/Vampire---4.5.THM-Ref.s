%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:27 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 566 expanded)
%              Number of leaves         :   33 ( 184 expanded)
%              Depth                    :   16
%              Number of atoms          :  666 (4031 expanded)
%              Number of equality atoms :  130 (1157 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f985,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f298,f345,f348,f368,f398,f515,f614,f618,f955,f961,f983])).

fof(f983,plain,(
    ~ spl9_66 ),
    inference(avatar_contradiction_clause,[],[f982])).

fof(f982,plain,
    ( $false
    | ~ spl9_66 ),
    inference(subsumption_resolution,[],[f981,f109])).

fof(f109,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f87,f62])).

fof(f62,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( sK5 != k2_relset_1(sK4,sK5,sK7)
    & k1_xboole_0 != sK6
    & v2_funct_1(sK8)
    & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f20,f49,f48])).

fof(f48,plain,
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
          ( sK5 != k2_relset_1(sK4,sK5,sK7)
          & k1_xboole_0 != sK6
          & v2_funct_1(X4)
          & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X4,sK5,sK6)
          & v1_funct_1(X4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X4] :
        ( sK5 != k2_relset_1(sK4,sK5,sK7)
        & k1_xboole_0 != sK6
        & v2_funct_1(X4)
        & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X4,sK5,sK6)
        & v1_funct_1(X4) )
   => ( sK5 != k2_relset_1(sK4,sK5,sK7)
      & k1_xboole_0 != sK6
      & v2_funct_1(sK8)
      & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f981,plain,
    ( ~ v1_relat_1(sK7)
    | ~ spl9_66 ),
    inference(subsumption_resolution,[],[f980,f121])).

fof(f121,plain,(
    v5_relat_1(sK7,sK5) ),
    inference(resolution,[],[f91,f62])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f980,plain,
    ( ~ v5_relat_1(sK7,sK5)
    | ~ v1_relat_1(sK7)
    | ~ spl9_66 ),
    inference(subsumption_resolution,[],[f978,f172])).

fof(f172,plain,(
    sK5 != k2_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f161,f62])).

fof(f161,plain,
    ( sK5 != k2_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f69,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f69,plain,(
    sK5 != k2_relset_1(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f978,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ v5_relat_1(sK7,sK5)
    | ~ v1_relat_1(sK7)
    | ~ spl9_66 ),
    inference(resolution,[],[f954,f118])).

fof(f118,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X2))
      | k2_relat_1(X2) = X1
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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

fof(f954,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f952])).

fof(f952,plain,
    ( spl9_66
  <=> r1_tarski(sK5,k2_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f961,plain,(
    spl9_61 ),
    inference(avatar_contradiction_clause,[],[f960])).

fof(f960,plain,
    ( $false
    | spl9_61 ),
    inference(subsumption_resolution,[],[f959,f110])).

fof(f110,plain,(
    v1_relat_1(sK8) ),
    inference(resolution,[],[f87,f65])).

fof(f65,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f50])).

fof(f959,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_61 ),
    inference(subsumption_resolution,[],[f958,f63])).

fof(f63,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f958,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_61 ),
    inference(subsumption_resolution,[],[f957,f67])).

fof(f67,plain,(
    v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f957,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_61 ),
    inference(resolution,[],[f956,f77])).

fof(f77,plain,(
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
    inference(definition_folding,[],[f24,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f956,plain,
    ( ~ sP0(sK8)
    | spl9_61 ),
    inference(resolution,[],[f928,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f928,plain,
    ( ~ v1_funct_1(k2_funct_1(sK8))
    | spl9_61 ),
    inference(avatar_component_clause,[],[f926])).

fof(f926,plain,
    ( spl9_61
  <=> v1_funct_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f955,plain,
    ( ~ spl9_61
    | spl9_66
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f950,f606,f394,f320,f291,f952,f926])).

fof(f291,plain,
    ( spl9_5
  <=> sK5 = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f320,plain,
    ( spl9_10
  <=> v1_relat_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f394,plain,
    ( spl9_16
  <=> sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f606,plain,
    ( spl9_51
  <=> sK6 = k2_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f950,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_51 ),
    inference(forward_demodulation,[],[f949,f649])).

fof(f649,plain,
    ( sK5 = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_51 ),
    inference(forward_demodulation,[],[f648,f293])).

fof(f293,plain,
    ( sK5 = k1_relat_1(sK8)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f291])).

fof(f648,plain,
    ( k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ spl9_10
    | ~ spl9_51 ),
    inference(subsumption_resolution,[],[f647,f63])).

fof(f647,plain,
    ( k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ v1_funct_1(sK8)
    | ~ spl9_10
    | ~ spl9_51 ),
    inference(subsumption_resolution,[],[f646,f67])).

fof(f646,plain,
    ( k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ spl9_10
    | ~ spl9_51 ),
    inference(subsumption_resolution,[],[f645,f110])).

fof(f645,plain,
    ( k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ v1_relat_1(sK8)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ spl9_10
    | ~ spl9_51 ),
    inference(subsumption_resolution,[],[f632,f321])).

fof(f321,plain,
    ( v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f320])).

fof(f632,plain,
    ( k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ v1_relat_1(sK8)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ spl9_51 ),
    inference(superposition,[],[f178,f608])).

fof(f608,plain,
    ( sK6 = k2_relat_1(sK8)
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f606])).

fof(f178,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(forward_demodulation,[],[f177,f71])).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f177,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) = k2_relat_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) = k2_relat_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f73,f78])).

fof(f78,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f949,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f948,f110])).

fof(f948,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f947,f63])).

fof(f947,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f946,f67])).

fof(f946,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f918,f321])).

fof(f918,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_16 ),
    inference(superposition,[],[f210,f532])).

fof(f532,plain,
    ( sK6 = k9_relat_1(sK8,k2_relat_1(sK7))
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f531,f109])).

fof(f531,plain,
    ( sK6 = k9_relat_1(sK8,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f516,f110])).

fof(f516,plain,
    ( sK6 = k9_relat_1(sK8,k2_relat_1(sK7))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7)
    | ~ spl9_16 ),
    inference(superposition,[],[f396,f73])).

fof(f396,plain,
    ( sK6 = k2_relat_1(k5_relat_1(sK7,sK8))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f394])).

fof(f210,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)),X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f82,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f618,plain,
    ( spl9_51
    | ~ spl9_16
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f617,f602,f394,f606])).

fof(f602,plain,
    ( spl9_50
  <=> r1_tarski(k2_relat_1(sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f617,plain,
    ( sK6 = k2_relat_1(sK8)
    | ~ spl9_16
    | ~ spl9_50 ),
    inference(subsumption_resolution,[],[f616,f536])).

fof(f536,plain,
    ( r1_tarski(sK6,k2_relat_1(sK8))
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f535,f109])).

fof(f535,plain,
    ( r1_tarski(sK6,k2_relat_1(sK8))
    | ~ v1_relat_1(sK7)
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f518,f110])).

fof(f518,plain,
    ( r1_tarski(sK6,k2_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7)
    | ~ spl9_16 ),
    inference(superposition,[],[f72,f396])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f616,plain,
    ( sK6 = k2_relat_1(sK8)
    | ~ r1_tarski(sK6,k2_relat_1(sK8))
    | ~ spl9_50 ),
    inference(resolution,[],[f603,f86])).

fof(f603,plain,
    ( r1_tarski(k2_relat_1(sK8),sK6)
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f602])).

fof(f614,plain,(
    spl9_50 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | spl9_50 ),
    inference(subsumption_resolution,[],[f612,f110])).

fof(f612,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_50 ),
    inference(subsumption_resolution,[],[f611,f122])).

fof(f122,plain,(
    v5_relat_1(sK8,sK6) ),
    inference(resolution,[],[f91,f65])).

fof(f611,plain,
    ( ~ v5_relat_1(sK8,sK6)
    | ~ v1_relat_1(sK8)
    | spl9_50 ),
    inference(resolution,[],[f604,f80])).

fof(f604,plain,
    ( ~ r1_tarski(k2_relat_1(sK8),sK6)
    | spl9_50 ),
    inference(avatar_component_clause,[],[f602])).

fof(f515,plain,
    ( spl9_15
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f514,f164,f390])).

fof(f390,plain,
    ( spl9_15
  <=> m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f164,plain,
    ( spl9_1
  <=> m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f514,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f513,f60])).

fof(f60,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f513,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f512,f62])).

fof(f512,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f511,f63])).

fof(f511,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f489,f65])).

fof(f489,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ spl9_1 ),
    inference(superposition,[],[f165,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f165,plain,
    ( m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f398,plain,
    ( ~ spl9_15
    | spl9_16 ),
    inference(avatar_split_clause,[],[f388,f394,f390])).

fof(f388,plain,
    ( sK6 = k2_relat_1(k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(superposition,[],[f89,f339])).

fof(f339,plain,(
    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) ),
    inference(subsumption_resolution,[],[f338,f60])).

fof(f338,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f337,f62])).

fof(f337,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f336,f63])).

fof(f336,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f329,f65])).

fof(f329,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(superposition,[],[f66,f100])).

fof(f66,plain,(
    sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f50])).

fof(f368,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f366,f60])).

fof(f366,plain,
    ( ~ v1_funct_1(sK7)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f365,f62])).

fof(f365,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f364,f63])).

fof(f364,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f355,f65])).

fof(f355,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl9_1 ),
    inference(resolution,[],[f102,f166])).

fof(f166,plain,
    ( ~ m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

% (27636)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (27630)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f348,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f346,f68])).

fof(f68,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f346,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_6 ),
    inference(resolution,[],[f297,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f297,plain,
    ( sP1(sK5,sK6)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl9_6
  <=> sP1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f345,plain,(
    spl9_10 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl9_10 ),
    inference(subsumption_resolution,[],[f343,f110])).

fof(f343,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_10 ),
    inference(subsumption_resolution,[],[f342,f63])).

fof(f342,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_10 ),
    inference(subsumption_resolution,[],[f341,f67])).

fof(f341,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_10 ),
    inference(resolution,[],[f340,f77])).

fof(f340,plain,
    ( ~ sP0(sK8)
    | spl9_10 ),
    inference(resolution,[],[f322,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f322,plain,
    ( ~ v1_relat_1(k2_funct_1(sK8))
    | spl9_10 ),
    inference(avatar_component_clause,[],[f320])).

fof(f298,plain,
    ( spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f289,f295,f291])).

fof(f289,plain,
    ( sP1(sK5,sK6)
    | sK5 = k1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f278,f64])).

fof(f64,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f278,plain,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | sP1(sK5,sK6)
    | sK5 = k1_relat_1(sK8) ),
    inference(resolution,[],[f219,f65])).

fof(f219,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f217,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f46,f45,f44])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f217,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f94,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:48:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (27635)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (27653)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (27634)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (27645)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (27651)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (27639)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.55  % (27650)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (27641)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  % (27643)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (27654)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (27631)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (27633)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (27642)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.57  % (27649)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.46/0.58  % (27632)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.46/0.58  % (27638)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.46/0.58  % (27655)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.46/0.58  % (27634)Refutation found. Thanks to Tanya!
% 1.46/0.58  % SZS status Theorem for theBenchmark
% 1.46/0.58  % SZS output start Proof for theBenchmark
% 1.46/0.58  fof(f985,plain,(
% 1.46/0.58    $false),
% 1.46/0.58    inference(avatar_sat_refutation,[],[f298,f345,f348,f368,f398,f515,f614,f618,f955,f961,f983])).
% 1.46/0.58  fof(f983,plain,(
% 1.46/0.58    ~spl9_66),
% 1.46/0.58    inference(avatar_contradiction_clause,[],[f982])).
% 1.46/0.58  fof(f982,plain,(
% 1.46/0.58    $false | ~spl9_66),
% 1.46/0.58    inference(subsumption_resolution,[],[f981,f109])).
% 1.46/0.58  fof(f109,plain,(
% 1.46/0.58    v1_relat_1(sK7)),
% 1.46/0.58    inference(resolution,[],[f87,f62])).
% 1.46/0.58  fof(f62,plain,(
% 1.46/0.58    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f50,plain,(
% 1.46/0.58    (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(sK8) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 1.46/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f20,f49,f48])).
% 1.46/0.58  fof(f48,plain,(
% 1.46/0.58    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(X4) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X4,sK5,sK6) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 1.46/0.58    introduced(choice_axiom,[])).
% 1.46/0.58  fof(f49,plain,(
% 1.46/0.58    ? [X4] : (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(X4) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X4,sK5,sK6) & v1_funct_1(X4)) => (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(sK8) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 1.46/0.58    introduced(choice_axiom,[])).
% 1.46/0.58  fof(f20,plain,(
% 1.46/0.58    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.46/0.58    inference(flattening,[],[f19])).
% 1.46/0.58  fof(f19,plain,(
% 1.46/0.58    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.46/0.58    inference(ennf_transformation,[],[f18])).
% 1.46/0.58  fof(f18,negated_conjecture,(
% 1.46/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.46/0.58    inference(negated_conjecture,[],[f17])).
% 1.46/0.58  fof(f17,conjecture,(
% 1.46/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 1.46/0.58  fof(f87,plain,(
% 1.46/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f32])).
% 1.46/0.58  fof(f32,plain,(
% 1.46/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.58    inference(ennf_transformation,[],[f10])).
% 1.46/0.58  fof(f10,axiom,(
% 1.46/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.46/0.58  fof(f981,plain,(
% 1.46/0.58    ~v1_relat_1(sK7) | ~spl9_66),
% 1.46/0.58    inference(subsumption_resolution,[],[f980,f121])).
% 1.46/0.58  fof(f121,plain,(
% 1.46/0.58    v5_relat_1(sK7,sK5)),
% 1.46/0.58    inference(resolution,[],[f91,f62])).
% 1.46/0.58  fof(f91,plain,(
% 1.46/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f35])).
% 1.46/0.58  fof(f35,plain,(
% 1.46/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.58    inference(ennf_transformation,[],[f11])).
% 1.46/0.58  fof(f11,axiom,(
% 1.46/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.46/0.58  fof(f980,plain,(
% 1.46/0.58    ~v5_relat_1(sK7,sK5) | ~v1_relat_1(sK7) | ~spl9_66),
% 1.46/0.58    inference(subsumption_resolution,[],[f978,f172])).
% 1.46/0.58  fof(f172,plain,(
% 1.46/0.58    sK5 != k2_relat_1(sK7)),
% 1.46/0.58    inference(subsumption_resolution,[],[f161,f62])).
% 1.46/0.58  fof(f161,plain,(
% 1.46/0.58    sK5 != k2_relat_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.46/0.58    inference(superposition,[],[f69,f89])).
% 1.46/0.58  fof(f89,plain,(
% 1.46/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.58    inference(cnf_transformation,[],[f34])).
% 1.46/0.58  fof(f34,plain,(
% 1.46/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.58    inference(ennf_transformation,[],[f13])).
% 1.46/0.58  fof(f13,axiom,(
% 1.46/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.46/0.58  fof(f69,plain,(
% 1.46/0.58    sK5 != k2_relset_1(sK4,sK5,sK7)),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f978,plain,(
% 1.46/0.58    sK5 = k2_relat_1(sK7) | ~v5_relat_1(sK7,sK5) | ~v1_relat_1(sK7) | ~spl9_66),
% 1.46/0.58    inference(resolution,[],[f954,f118])).
% 1.46/0.58  fof(f118,plain,(
% 1.46/0.58    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(X2)) | k2_relat_1(X2) = X1 | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.46/0.58    inference(resolution,[],[f86,f80])).
% 1.46/0.58  fof(f80,plain,(
% 1.46/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f52])).
% 1.46/0.58  fof(f52,plain,(
% 1.46/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.46/0.58    inference(nnf_transformation,[],[f27])).
% 1.46/0.58  fof(f27,plain,(
% 1.46/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.46/0.58    inference(ennf_transformation,[],[f2])).
% 1.46/0.58  fof(f2,axiom,(
% 1.46/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.46/0.58  fof(f86,plain,(
% 1.46/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f54])).
% 1.46/0.58  fof(f54,plain,(
% 1.46/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.58    inference(flattening,[],[f53])).
% 1.46/0.58  fof(f53,plain,(
% 1.46/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.58    inference(nnf_transformation,[],[f1])).
% 1.46/0.58  fof(f1,axiom,(
% 1.46/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.58  fof(f954,plain,(
% 1.46/0.58    r1_tarski(sK5,k2_relat_1(sK7)) | ~spl9_66),
% 1.46/0.58    inference(avatar_component_clause,[],[f952])).
% 1.46/0.58  fof(f952,plain,(
% 1.46/0.58    spl9_66 <=> r1_tarski(sK5,k2_relat_1(sK7))),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).
% 1.46/0.58  fof(f961,plain,(
% 1.46/0.58    spl9_61),
% 1.46/0.58    inference(avatar_contradiction_clause,[],[f960])).
% 1.46/0.58  fof(f960,plain,(
% 1.46/0.58    $false | spl9_61),
% 1.46/0.58    inference(subsumption_resolution,[],[f959,f110])).
% 1.46/0.58  fof(f110,plain,(
% 1.46/0.58    v1_relat_1(sK8)),
% 1.46/0.58    inference(resolution,[],[f87,f65])).
% 1.46/0.58  fof(f65,plain,(
% 1.46/0.58    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f959,plain,(
% 1.46/0.58    ~v1_relat_1(sK8) | spl9_61),
% 1.46/0.58    inference(subsumption_resolution,[],[f958,f63])).
% 1.46/0.58  fof(f63,plain,(
% 1.46/0.58    v1_funct_1(sK8)),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f958,plain,(
% 1.46/0.58    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_61),
% 1.46/0.58    inference(subsumption_resolution,[],[f957,f67])).
% 1.46/0.58  fof(f67,plain,(
% 1.46/0.58    v2_funct_1(sK8)),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f957,plain,(
% 1.46/0.58    ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_61),
% 1.46/0.58    inference(resolution,[],[f956,f77])).
% 1.46/0.58  fof(f77,plain,(
% 1.46/0.58    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f43])).
% 1.46/0.58  fof(f43,plain,(
% 1.46/0.58    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(definition_folding,[],[f24,f42])).
% 1.46/0.58  fof(f42,plain,(
% 1.46/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 1.46/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.46/0.58  fof(f24,plain,(
% 1.46/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(flattening,[],[f23])).
% 1.46/0.58  fof(f23,plain,(
% 1.46/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.58    inference(ennf_transformation,[],[f6])).
% 1.46/0.58  fof(f6,axiom,(
% 1.46/0.58    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.46/0.58  fof(f956,plain,(
% 1.46/0.58    ~sP0(sK8) | spl9_61),
% 1.46/0.58    inference(resolution,[],[f928,f75])).
% 1.46/0.58  fof(f75,plain,(
% 1.46/0.58    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f51])).
% 1.46/0.58  fof(f51,plain,(
% 1.46/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 1.46/0.58    inference(nnf_transformation,[],[f42])).
% 1.46/0.58  fof(f928,plain,(
% 1.46/0.58    ~v1_funct_1(k2_funct_1(sK8)) | spl9_61),
% 1.46/0.58    inference(avatar_component_clause,[],[f926])).
% 1.46/0.58  fof(f926,plain,(
% 1.46/0.58    spl9_61 <=> v1_funct_1(k2_funct_1(sK8))),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).
% 1.46/0.58  fof(f955,plain,(
% 1.46/0.58    ~spl9_61 | spl9_66 | ~spl9_5 | ~spl9_10 | ~spl9_16 | ~spl9_51),
% 1.46/0.58    inference(avatar_split_clause,[],[f950,f606,f394,f320,f291,f952,f926])).
% 1.46/0.58  fof(f291,plain,(
% 1.46/0.58    spl9_5 <=> sK5 = k1_relat_1(sK8)),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.46/0.58  fof(f320,plain,(
% 1.46/0.58    spl9_10 <=> v1_relat_1(k2_funct_1(sK8))),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.46/0.58  fof(f394,plain,(
% 1.46/0.58    spl9_16 <=> sK6 = k2_relat_1(k5_relat_1(sK7,sK8))),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.46/0.58  fof(f606,plain,(
% 1.46/0.58    spl9_51 <=> sK6 = k2_relat_1(sK8)),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).
% 1.46/0.58  fof(f950,plain,(
% 1.46/0.58    r1_tarski(sK5,k2_relat_1(sK7)) | ~v1_funct_1(k2_funct_1(sK8)) | (~spl9_5 | ~spl9_10 | ~spl9_16 | ~spl9_51)),
% 1.46/0.58    inference(forward_demodulation,[],[f949,f649])).
% 1.46/0.58  fof(f649,plain,(
% 1.46/0.58    sK5 = k9_relat_1(k2_funct_1(sK8),sK6) | (~spl9_5 | ~spl9_10 | ~spl9_51)),
% 1.46/0.58    inference(forward_demodulation,[],[f648,f293])).
% 1.46/0.58  fof(f293,plain,(
% 1.46/0.58    sK5 = k1_relat_1(sK8) | ~spl9_5),
% 1.46/0.58    inference(avatar_component_clause,[],[f291])).
% 1.46/0.58  fof(f648,plain,(
% 1.46/0.58    k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6) | (~spl9_10 | ~spl9_51)),
% 1.46/0.58    inference(subsumption_resolution,[],[f647,f63])).
% 1.46/0.58  fof(f647,plain,(
% 1.46/0.58    k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6) | ~v1_funct_1(sK8) | (~spl9_10 | ~spl9_51)),
% 1.46/0.58    inference(subsumption_resolution,[],[f646,f67])).
% 1.46/0.58  fof(f646,plain,(
% 1.46/0.58    k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | (~spl9_10 | ~spl9_51)),
% 1.46/0.58    inference(subsumption_resolution,[],[f645,f110])).
% 1.46/0.58  fof(f645,plain,(
% 1.46/0.58    k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6) | ~v1_relat_1(sK8) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | (~spl9_10 | ~spl9_51)),
% 1.46/0.58    inference(subsumption_resolution,[],[f632,f321])).
% 1.46/0.58  fof(f321,plain,(
% 1.46/0.58    v1_relat_1(k2_funct_1(sK8)) | ~spl9_10),
% 1.46/0.58    inference(avatar_component_clause,[],[f320])).
% 1.46/0.58  fof(f632,plain,(
% 1.46/0.58    k1_relat_1(sK8) = k9_relat_1(k2_funct_1(sK8),sK6) | ~v1_relat_1(k2_funct_1(sK8)) | ~v1_relat_1(sK8) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~spl9_51),
% 1.46/0.58    inference(superposition,[],[f178,f608])).
% 1.46/0.58  fof(f608,plain,(
% 1.46/0.58    sK6 = k2_relat_1(sK8) | ~spl9_51),
% 1.46/0.58    inference(avatar_component_clause,[],[f606])).
% 1.46/0.58  fof(f178,plain,(
% 1.46/0.58    ( ! [X0] : (k1_relat_1(X0) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 1.46/0.58    inference(forward_demodulation,[],[f177,f71])).
% 1.46/0.58  fof(f71,plain,(
% 1.46/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.46/0.58    inference(cnf_transformation,[],[f5])).
% 1.46/0.58  fof(f5,axiom,(
% 1.46/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.46/0.58  fof(f177,plain,(
% 1.46/0.58    ( ! [X0] : (k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) = k2_relat_1(k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 1.46/0.58    inference(duplicate_literal_removal,[],[f174])).
% 1.46/0.58  fof(f174,plain,(
% 1.46/0.58    ( ! [X0] : (k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) = k2_relat_1(k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(superposition,[],[f73,f78])).
% 1.46/0.58  fof(f78,plain,(
% 1.46/0.58    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f26])).
% 1.46/0.58  fof(f26,plain,(
% 1.46/0.58    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(flattening,[],[f25])).
% 1.46/0.58  fof(f25,plain,(
% 1.46/0.58    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.58    inference(ennf_transformation,[],[f9])).
% 1.46/0.58  fof(f9,axiom,(
% 1.46/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.46/0.58  fof(f73,plain,(
% 1.46/0.58    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f22])).
% 1.46/0.58  fof(f22,plain,(
% 1.46/0.58    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(ennf_transformation,[],[f3])).
% 1.46/0.58  fof(f3,axiom,(
% 1.46/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.46/0.58  fof(f949,plain,(
% 1.46/0.58    r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7)) | ~v1_funct_1(k2_funct_1(sK8)) | (~spl9_10 | ~spl9_16)),
% 1.46/0.58    inference(subsumption_resolution,[],[f948,f110])).
% 1.46/0.58  fof(f948,plain,(
% 1.46/0.58    r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7)) | ~v1_funct_1(k2_funct_1(sK8)) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16)),
% 1.46/0.58    inference(subsumption_resolution,[],[f947,f63])).
% 1.46/0.58  fof(f947,plain,(
% 1.46/0.58    r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7)) | ~v1_funct_1(k2_funct_1(sK8)) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16)),
% 1.46/0.58    inference(subsumption_resolution,[],[f946,f67])).
% 1.46/0.58  fof(f946,plain,(
% 1.46/0.58    r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7)) | ~v1_funct_1(k2_funct_1(sK8)) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16)),
% 1.46/0.58    inference(subsumption_resolution,[],[f918,f321])).
% 1.46/0.58  fof(f918,plain,(
% 1.46/0.58    r1_tarski(k9_relat_1(k2_funct_1(sK8),sK6),k2_relat_1(sK7)) | ~v1_funct_1(k2_funct_1(sK8)) | ~v1_relat_1(k2_funct_1(sK8)) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_16),
% 1.46/0.58    inference(superposition,[],[f210,f532])).
% 1.46/0.58  fof(f532,plain,(
% 1.46/0.58    sK6 = k9_relat_1(sK8,k2_relat_1(sK7)) | ~spl9_16),
% 1.46/0.58    inference(subsumption_resolution,[],[f531,f109])).
% 1.46/0.58  fof(f531,plain,(
% 1.46/0.58    sK6 = k9_relat_1(sK8,k2_relat_1(sK7)) | ~v1_relat_1(sK7) | ~spl9_16),
% 1.46/0.58    inference(subsumption_resolution,[],[f516,f110])).
% 1.46/0.58  fof(f516,plain,(
% 1.46/0.58    sK6 = k9_relat_1(sK8,k2_relat_1(sK7)) | ~v1_relat_1(sK8) | ~v1_relat_1(sK7) | ~spl9_16),
% 1.46/0.58    inference(superposition,[],[f396,f73])).
% 1.46/0.58  fof(f396,plain,(
% 1.46/0.58    sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) | ~spl9_16),
% 1.46/0.58    inference(avatar_component_clause,[],[f394])).
% 1.46/0.58  fof(f210,plain,(
% 1.46/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)),X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(superposition,[],[f82,f83])).
% 1.46/0.58  fof(f83,plain,(
% 1.46/0.58    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f31])).
% 1.46/0.58  fof(f31,plain,(
% 1.46/0.58    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.58    inference(flattening,[],[f30])).
% 1.46/0.58  fof(f30,plain,(
% 1.46/0.58    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.46/0.58    inference(ennf_transformation,[],[f8])).
% 1.46/0.58  fof(f8,axiom,(
% 1.46/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.46/0.58  fof(f82,plain,(
% 1.46/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f29])).
% 1.46/0.58  fof(f29,plain,(
% 1.46/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.58    inference(flattening,[],[f28])).
% 1.46/0.58  fof(f28,plain,(
% 1.46/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.46/0.58    inference(ennf_transformation,[],[f7])).
% 1.46/0.58  fof(f7,axiom,(
% 1.46/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.46/0.58  fof(f618,plain,(
% 1.46/0.58    spl9_51 | ~spl9_16 | ~spl9_50),
% 1.46/0.58    inference(avatar_split_clause,[],[f617,f602,f394,f606])).
% 1.46/0.58  fof(f602,plain,(
% 1.46/0.58    spl9_50 <=> r1_tarski(k2_relat_1(sK8),sK6)),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 1.46/0.58  fof(f617,plain,(
% 1.46/0.58    sK6 = k2_relat_1(sK8) | (~spl9_16 | ~spl9_50)),
% 1.46/0.58    inference(subsumption_resolution,[],[f616,f536])).
% 1.46/0.58  fof(f536,plain,(
% 1.46/0.58    r1_tarski(sK6,k2_relat_1(sK8)) | ~spl9_16),
% 1.46/0.58    inference(subsumption_resolution,[],[f535,f109])).
% 1.46/0.58  fof(f535,plain,(
% 1.46/0.58    r1_tarski(sK6,k2_relat_1(sK8)) | ~v1_relat_1(sK7) | ~spl9_16),
% 1.46/0.58    inference(subsumption_resolution,[],[f518,f110])).
% 1.46/0.58  fof(f518,plain,(
% 1.46/0.58    r1_tarski(sK6,k2_relat_1(sK8)) | ~v1_relat_1(sK8) | ~v1_relat_1(sK7) | ~spl9_16),
% 1.46/0.58    inference(superposition,[],[f72,f396])).
% 1.46/0.58  fof(f72,plain,(
% 1.46/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f21])).
% 1.46/0.58  fof(f21,plain,(
% 1.46/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(ennf_transformation,[],[f4])).
% 1.46/0.58  fof(f4,axiom,(
% 1.46/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.46/0.58  fof(f616,plain,(
% 1.46/0.58    sK6 = k2_relat_1(sK8) | ~r1_tarski(sK6,k2_relat_1(sK8)) | ~spl9_50),
% 1.46/0.58    inference(resolution,[],[f603,f86])).
% 1.46/0.58  fof(f603,plain,(
% 1.46/0.58    r1_tarski(k2_relat_1(sK8),sK6) | ~spl9_50),
% 1.46/0.58    inference(avatar_component_clause,[],[f602])).
% 1.46/0.58  fof(f614,plain,(
% 1.46/0.58    spl9_50),
% 1.46/0.58    inference(avatar_contradiction_clause,[],[f613])).
% 1.46/0.58  fof(f613,plain,(
% 1.46/0.58    $false | spl9_50),
% 1.46/0.58    inference(subsumption_resolution,[],[f612,f110])).
% 1.46/0.58  fof(f612,plain,(
% 1.46/0.58    ~v1_relat_1(sK8) | spl9_50),
% 1.46/0.58    inference(subsumption_resolution,[],[f611,f122])).
% 1.46/0.58  fof(f122,plain,(
% 1.46/0.58    v5_relat_1(sK8,sK6)),
% 1.46/0.58    inference(resolution,[],[f91,f65])).
% 1.46/0.58  fof(f611,plain,(
% 1.46/0.58    ~v5_relat_1(sK8,sK6) | ~v1_relat_1(sK8) | spl9_50),
% 1.46/0.58    inference(resolution,[],[f604,f80])).
% 1.46/0.58  fof(f604,plain,(
% 1.46/0.58    ~r1_tarski(k2_relat_1(sK8),sK6) | spl9_50),
% 1.46/0.58    inference(avatar_component_clause,[],[f602])).
% 1.46/0.58  fof(f515,plain,(
% 1.46/0.58    spl9_15 | ~spl9_1),
% 1.46/0.58    inference(avatar_split_clause,[],[f514,f164,f390])).
% 1.46/0.58  fof(f390,plain,(
% 1.46/0.58    spl9_15 <=> m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.46/0.58  fof(f164,plain,(
% 1.46/0.58    spl9_1 <=> m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.46/0.58  fof(f514,plain,(
% 1.46/0.58    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~spl9_1),
% 1.46/0.58    inference(subsumption_resolution,[],[f513,f60])).
% 1.46/0.58  fof(f60,plain,(
% 1.46/0.58    v1_funct_1(sK7)),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f513,plain,(
% 1.46/0.58    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_1(sK7) | ~spl9_1),
% 1.46/0.58    inference(subsumption_resolution,[],[f512,f62])).
% 1.46/0.58  fof(f512,plain,(
% 1.46/0.58    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~spl9_1),
% 1.46/0.58    inference(subsumption_resolution,[],[f511,f63])).
% 1.46/0.58  fof(f511,plain,(
% 1.46/0.58    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~spl9_1),
% 1.46/0.58    inference(subsumption_resolution,[],[f489,f65])).
% 1.46/0.58  fof(f489,plain,(
% 1.46/0.58    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~spl9_1),
% 1.46/0.58    inference(superposition,[],[f165,f100])).
% 1.46/0.58  fof(f100,plain,(
% 1.46/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f39])).
% 1.46/0.58  fof(f39,plain,(
% 1.46/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.46/0.58    inference(flattening,[],[f38])).
% 1.46/0.58  fof(f38,plain,(
% 1.46/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.46/0.58    inference(ennf_transformation,[],[f16])).
% 1.46/0.58  fof(f16,axiom,(
% 1.46/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.46/0.58  fof(f165,plain,(
% 1.46/0.58    m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~spl9_1),
% 1.46/0.58    inference(avatar_component_clause,[],[f164])).
% 1.46/0.58  fof(f398,plain,(
% 1.46/0.58    ~spl9_15 | spl9_16),
% 1.46/0.58    inference(avatar_split_clause,[],[f388,f394,f390])).
% 1.46/0.58  fof(f388,plain,(
% 1.46/0.58    sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) | ~m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 1.46/0.58    inference(superposition,[],[f89,f339])).
% 1.46/0.58  fof(f339,plain,(
% 1.46/0.58    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))),
% 1.46/0.58    inference(subsumption_resolution,[],[f338,f60])).
% 1.46/0.58  fof(f338,plain,(
% 1.46/0.58    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~v1_funct_1(sK7)),
% 1.46/0.58    inference(subsumption_resolution,[],[f337,f62])).
% 1.46/0.58  fof(f337,plain,(
% 1.46/0.58    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 1.46/0.58    inference(subsumption_resolution,[],[f336,f63])).
% 1.46/0.58  fof(f336,plain,(
% 1.46/0.58    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 1.46/0.58    inference(subsumption_resolution,[],[f329,f65])).
% 1.46/0.58  fof(f329,plain,(
% 1.46/0.58    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 1.46/0.58    inference(superposition,[],[f66,f100])).
% 1.46/0.58  fof(f66,plain,(
% 1.46/0.58    sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f368,plain,(
% 1.46/0.58    spl9_1),
% 1.46/0.58    inference(avatar_contradiction_clause,[],[f367])).
% 1.46/0.58  fof(f367,plain,(
% 1.46/0.58    $false | spl9_1),
% 1.46/0.58    inference(subsumption_resolution,[],[f366,f60])).
% 1.46/0.58  fof(f366,plain,(
% 1.46/0.58    ~v1_funct_1(sK7) | spl9_1),
% 1.46/0.58    inference(subsumption_resolution,[],[f365,f62])).
% 1.46/0.58  fof(f365,plain,(
% 1.46/0.58    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl9_1),
% 1.46/0.58    inference(subsumption_resolution,[],[f364,f63])).
% 1.46/0.58  fof(f364,plain,(
% 1.46/0.58    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl9_1),
% 1.46/0.58    inference(subsumption_resolution,[],[f355,f65])).
% 1.46/0.58  fof(f355,plain,(
% 1.46/0.58    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl9_1),
% 1.46/0.58    inference(resolution,[],[f102,f166])).
% 1.46/0.58  fof(f166,plain,(
% 1.46/0.58    ~m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | spl9_1),
% 1.46/0.58    inference(avatar_component_clause,[],[f164])).
% 1.46/0.58  fof(f102,plain,(
% 1.46/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f41])).
% 1.46/0.58  fof(f41,plain,(
% 1.46/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.46/0.58    inference(flattening,[],[f40])).
% 1.46/0.58  fof(f40,plain,(
% 1.46/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.46/0.58    inference(ennf_transformation,[],[f15])).
% 1.46/0.58  fof(f15,axiom,(
% 1.46/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.46/0.58  % (27636)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.46/0.58  % (27630)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.46/0.58  fof(f348,plain,(
% 1.46/0.58    ~spl9_6),
% 1.46/0.58    inference(avatar_contradiction_clause,[],[f347])).
% 1.46/0.58  fof(f347,plain,(
% 1.46/0.58    $false | ~spl9_6),
% 1.46/0.58    inference(subsumption_resolution,[],[f346,f68])).
% 1.46/0.58  fof(f68,plain,(
% 1.46/0.58    k1_xboole_0 != sK6),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f346,plain,(
% 1.46/0.58    k1_xboole_0 = sK6 | ~spl9_6),
% 1.46/0.58    inference(resolution,[],[f297,f96])).
% 1.46/0.58  fof(f96,plain,(
% 1.46/0.58    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 1.46/0.58    inference(cnf_transformation,[],[f59])).
% 1.46/0.58  fof(f59,plain,(
% 1.46/0.58    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.46/0.58    inference(nnf_transformation,[],[f44])).
% 1.46/0.58  fof(f44,plain,(
% 1.46/0.58    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.46/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.46/0.58  fof(f297,plain,(
% 1.46/0.58    sP1(sK5,sK6) | ~spl9_6),
% 1.46/0.58    inference(avatar_component_clause,[],[f295])).
% 1.46/0.58  fof(f295,plain,(
% 1.46/0.58    spl9_6 <=> sP1(sK5,sK6)),
% 1.46/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.46/0.58  fof(f345,plain,(
% 1.46/0.58    spl9_10),
% 1.46/0.58    inference(avatar_contradiction_clause,[],[f344])).
% 1.46/0.58  fof(f344,plain,(
% 1.46/0.58    $false | spl9_10),
% 1.46/0.58    inference(subsumption_resolution,[],[f343,f110])).
% 1.46/0.58  fof(f343,plain,(
% 1.46/0.58    ~v1_relat_1(sK8) | spl9_10),
% 1.46/0.58    inference(subsumption_resolution,[],[f342,f63])).
% 1.46/0.58  fof(f342,plain,(
% 1.46/0.58    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_10),
% 1.46/0.58    inference(subsumption_resolution,[],[f341,f67])).
% 1.46/0.58  fof(f341,plain,(
% 1.46/0.58    ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_10),
% 1.46/0.58    inference(resolution,[],[f340,f77])).
% 1.46/0.58  fof(f340,plain,(
% 1.46/0.58    ~sP0(sK8) | spl9_10),
% 1.46/0.58    inference(resolution,[],[f322,f74])).
% 1.46/0.58  fof(f74,plain,(
% 1.46/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f51])).
% 1.46/0.58  fof(f322,plain,(
% 1.46/0.58    ~v1_relat_1(k2_funct_1(sK8)) | spl9_10),
% 1.46/0.58    inference(avatar_component_clause,[],[f320])).
% 1.46/0.58  fof(f298,plain,(
% 1.46/0.58    spl9_5 | spl9_6),
% 1.46/0.58    inference(avatar_split_clause,[],[f289,f295,f291])).
% 1.46/0.58  fof(f289,plain,(
% 1.46/0.58    sP1(sK5,sK6) | sK5 = k1_relat_1(sK8)),
% 1.46/0.58    inference(subsumption_resolution,[],[f278,f64])).
% 1.46/0.58  fof(f64,plain,(
% 1.46/0.58    v1_funct_2(sK8,sK5,sK6)),
% 1.46/0.58    inference(cnf_transformation,[],[f50])).
% 1.46/0.58  fof(f278,plain,(
% 1.46/0.58    ~v1_funct_2(sK8,sK5,sK6) | sP1(sK5,sK6) | sK5 = k1_relat_1(sK8)),
% 1.46/0.58    inference(resolution,[],[f219,f65])).
% 1.46/0.58  fof(f219,plain,(
% 1.46/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.46/0.58    inference(subsumption_resolution,[],[f217,f98])).
% 1.46/0.58  fof(f98,plain,(
% 1.46/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f47])).
% 1.46/0.58  fof(f47,plain,(
% 1.46/0.58    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.58    inference(definition_folding,[],[f37,f46,f45,f44])).
% 1.46/0.58  fof(f45,plain,(
% 1.46/0.58    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.46/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.46/0.58  fof(f46,plain,(
% 1.46/0.58    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 1.46/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.46/0.58  fof(f37,plain,(
% 1.46/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.58    inference(flattening,[],[f36])).
% 1.46/0.58  fof(f36,plain,(
% 1.46/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.58    inference(ennf_transformation,[],[f14])).
% 1.46/0.58  fof(f14,axiom,(
% 1.46/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.46/0.58  fof(f217,plain,(
% 1.46/0.58    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.46/0.58    inference(superposition,[],[f94,f88])).
% 1.46/0.58  fof(f88,plain,(
% 1.46/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.58    inference(cnf_transformation,[],[f33])).
% 1.46/0.58  fof(f33,plain,(
% 1.46/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.58    inference(ennf_transformation,[],[f12])).
% 1.46/0.58  fof(f12,axiom,(
% 1.46/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.46/0.58  fof(f94,plain,(
% 1.46/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f58])).
% 1.46/0.58  fof(f58,plain,(
% 1.46/0.58    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 1.46/0.58    inference(rectify,[],[f57])).
% 1.46/0.58  fof(f57,plain,(
% 1.46/0.58    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.46/0.58    inference(nnf_transformation,[],[f45])).
% 1.46/0.58  % SZS output end Proof for theBenchmark
% 1.46/0.58  % (27634)------------------------------
% 1.46/0.58  % (27634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (27634)Termination reason: Refutation
% 1.46/0.59  
% 1.46/0.59  % (27634)Memory used [KB]: 6652
% 1.46/0.59  % (27634)Time elapsed: 0.159 s
% 1.46/0.59  % (27634)------------------------------
% 1.46/0.59  % (27634)------------------------------
% 1.46/0.59  % (27629)Success in time 0.224 s
%------------------------------------------------------------------------------
