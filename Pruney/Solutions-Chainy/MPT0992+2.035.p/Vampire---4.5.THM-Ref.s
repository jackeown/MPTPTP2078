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
% DateTime   : Thu Dec  3 13:03:15 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 736 expanded)
%              Number of leaves         :   29 ( 191 expanded)
%              Depth                    :   17
%              Number of atoms          :  530 (4192 expanded)
%              Number of equality atoms :  114 ( 930 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f126,f180,f288,f297,f484,f502,f505,f696,f944,f1000,f1186])).

fof(f1186,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f1185])).

fof(f1185,plain,
    ( $false
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f1180,f1124])).

fof(f1124,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f1097,f291])).

fof(f291,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f290,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f290,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f177,f120])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f177,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_11
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1097,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f1005,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1005,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f55,f120])).

fof(f55,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f1180,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f1141,f1149])).

fof(f1149,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f1148,f60])).

fof(f60,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1148,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(resolution,[],[f1100,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f1100,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f143,f291])).

fof(f143,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f1141,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f1140,f291])).

fof(f1140,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f417,f120])).

fof(f417,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl5_2
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f196,f414])).

fof(f414,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f413,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f413,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f293,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f57,f125])).

fof(f57,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f196,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl5_2 ),
    inference(backward_demodulation,[],[f112,f146])).

fof(f146,plain,(
    ! [X1] : k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f139,plain,(
    ! [X1] :
      ( k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f56,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f112,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1000,plain,
    ( spl5_15
    | spl5_4 ),
    inference(avatar_split_clause,[],[f317,f119,f266])).

fof(f266,plain,
    ( spl5_15
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f317,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f310,f55])).

fof(f310,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f56,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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

fof(f944,plain,
    ( spl5_3
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f943])).

fof(f943,plain,
    ( $false
    | spl5_3
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f933,f222])).

fof(f222,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f219,f154])).

fof(f154,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f153,f103])).

fof(f103,plain,(
    ! [X2,X0] :
      ( sP4(X2)
      | v1_relat_1(k7_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f103_D])).

fof(f103_D,plain,(
    ! [X2] :
      ( ! [X0] : v1_relat_1(k7_relat_1(X2,X0))
    <=> ~ sP4(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f153,plain,(
    ~ sP4(sK3) ),
    inference(subsumption_resolution,[],[f151,f143])).

fof(f151,plain,
    ( ~ v1_relat_1(sK3)
    | ~ sP4(sK3) ),
    inference(resolution,[],[f141,f104])).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ sP4(X2) ) ),
    inference(general_splitting,[],[f89,f103_D])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

fof(f141,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f56,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f219,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f211,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f211,plain,(
    ! [X5] : v5_relat_1(k7_relat_1(sK3,X5),sK1) ),
    inference(resolution,[],[f199,f82])).

fof(f199,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f198,f54])).

fof(f198,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f197,f56])).

fof(f197,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f93,f146])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f933,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl5_3
    | ~ spl5_15 ),
    inference(resolution,[],[f601,f697])).

fof(f697,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f116,f146])).

fof(f116,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f601,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f600,f154])).

fof(f600,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f596,f195])).

fof(f195,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f145,f146])).

fof(f145,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f138,f54])).

fof(f138,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f56,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f596,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl5_15 ),
    inference(superposition,[],[f70,f588])).

fof(f588,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl5_15 ),
    inference(resolution,[],[f358,f57])).

fof(f358,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f351,f143])).

fof(f351,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | ~ spl5_15 ),
    inference(superposition,[],[f65,f348])).

fof(f348,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f142,f268])).

fof(f268,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f266])).

fof(f142,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f56,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f696,plain,
    ( spl5_2
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | spl5_2
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f694,f196])).

fof(f694,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl5_15 ),
    inference(resolution,[],[f599,f222])).

fof(f599,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) )
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f598,f154])).

fof(f598,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f595,f195])).

fof(f595,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl5_15 ),
    inference(superposition,[],[f69,f588])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f505,plain,
    ( ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f504,f134,f130])).

fof(f130,plain,
    ( spl5_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f134,plain,
    ( spl5_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f504,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f57,f73])).

fof(f502,plain,
    ( spl5_3
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f500,f54])).

fof(f500,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f498,f56])).

fof(f498,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f495,f93])).

fof(f495,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_3
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f116,f136])).

fof(f136,plain,
    ( sK0 = sK2
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f484,plain,
    ( ~ spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f483,f175,f171])).

fof(f171,plain,
    ( spl5_10
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f483,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    inference(resolution,[],[f144,f73])).

fof(f144,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f56,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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

fof(f297,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl5_5
    | spl5_6 ),
    inference(subsumption_resolution,[],[f295,f62])).

fof(f295,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_5
    | spl5_6 ),
    inference(backward_demodulation,[],[f132,f125])).

fof(f132,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f288,plain,
    ( ~ spl5_4
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl5_4
    | spl5_10 ),
    inference(subsumption_resolution,[],[f286,f62])).

fof(f286,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_4
    | spl5_10 ),
    inference(forward_demodulation,[],[f277,f96])).

fof(f277,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | ~ spl5_4
    | spl5_10 ),
    inference(backward_demodulation,[],[f173,f120])).

fof(f173,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f171])).

fof(f180,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f145,f108])).

fof(f108,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f126,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f58,f123,f119])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f117,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f59,f114,f110,f106])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:46:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (12374)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (12392)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (12373)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.56  % (12394)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (12380)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (12391)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (12386)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.56  % (12372)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (12377)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.57  % (12375)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.57  % (12376)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.57  % (12384)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.58  % (12388)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.58  % (12396)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.58  % (12390)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.58  % (12393)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.57/0.59  % (12381)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.57/0.59  % (12383)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.57/0.60  % (12371)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.57/0.60  % (12379)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.57/0.60  % (12389)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.91/0.61  % (12382)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.91/0.61  % (12385)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.91/0.64  % (12395)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.91/0.64  % (12372)Refutation found. Thanks to Tanya!
% 1.91/0.64  % SZS status Theorem for theBenchmark
% 1.91/0.64  % SZS output start Proof for theBenchmark
% 1.91/0.64  fof(f1187,plain,(
% 1.91/0.64    $false),
% 1.91/0.64    inference(avatar_sat_refutation,[],[f117,f126,f180,f288,f297,f484,f502,f505,f696,f944,f1000,f1186])).
% 1.91/0.64  fof(f1186,plain,(
% 1.91/0.64    spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_11),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f1185])).
% 1.91/0.64  fof(f1185,plain,(
% 1.91/0.64    $false | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.91/0.64    inference(subsumption_resolution,[],[f1180,f1124])).
% 1.91/0.64  fof(f1124,plain,(
% 1.91/0.64    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.91/0.64    inference(forward_demodulation,[],[f1097,f291])).
% 1.91/0.64  fof(f291,plain,(
% 1.91/0.64    k1_xboole_0 = sK3 | (~spl5_4 | ~spl5_11)),
% 1.91/0.64    inference(forward_demodulation,[],[f290,f96])).
% 1.91/0.64  fof(f96,plain,(
% 1.91/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.91/0.64    inference(equality_resolution,[],[f78])).
% 1.91/0.64  fof(f78,plain,(
% 1.91/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.91/0.64    inference(cnf_transformation,[],[f52])).
% 1.91/0.64  fof(f52,plain,(
% 1.91/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.91/0.64    inference(flattening,[],[f51])).
% 1.91/0.64  fof(f51,plain,(
% 1.91/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.91/0.64    inference(nnf_transformation,[],[f3])).
% 1.91/0.64  fof(f3,axiom,(
% 1.91/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.91/0.64  fof(f290,plain,(
% 1.91/0.64    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl5_4 | ~spl5_11)),
% 1.91/0.64    inference(forward_demodulation,[],[f177,f120])).
% 1.91/0.64  fof(f120,plain,(
% 1.91/0.64    k1_xboole_0 = sK1 | ~spl5_4),
% 1.91/0.64    inference(avatar_component_clause,[],[f119])).
% 1.91/0.64  fof(f119,plain,(
% 1.91/0.64    spl5_4 <=> k1_xboole_0 = sK1),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.91/0.64  fof(f177,plain,(
% 1.91/0.64    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl5_11),
% 1.91/0.64    inference(avatar_component_clause,[],[f175])).
% 1.91/0.64  fof(f175,plain,(
% 1.91/0.64    spl5_11 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.91/0.64  fof(f1097,plain,(
% 1.91/0.64    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_5)),
% 1.91/0.64    inference(forward_demodulation,[],[f1005,f125])).
% 1.91/0.64  fof(f125,plain,(
% 1.91/0.64    k1_xboole_0 = sK0 | ~spl5_5),
% 1.91/0.64    inference(avatar_component_clause,[],[f123])).
% 1.91/0.64  fof(f123,plain,(
% 1.91/0.64    spl5_5 <=> k1_xboole_0 = sK0),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.91/0.64  fof(f1005,plain,(
% 1.91/0.64    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl5_4),
% 1.91/0.64    inference(backward_demodulation,[],[f55,f120])).
% 1.91/0.64  fof(f55,plain,(
% 1.91/0.64    v1_funct_2(sK3,sK0,sK1)),
% 1.91/0.64    inference(cnf_transformation,[],[f46])).
% 1.91/0.64  fof(f46,plain,(
% 1.91/0.64    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.91/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45])).
% 1.91/0.64  fof(f45,plain,(
% 1.91/0.64    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.91/0.64    introduced(choice_axiom,[])).
% 1.91/0.64  fof(f25,plain,(
% 1.91/0.64    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.91/0.64    inference(flattening,[],[f24])).
% 1.91/0.64  fof(f24,plain,(
% 1.91/0.64    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.91/0.64    inference(ennf_transformation,[],[f21])).
% 1.91/0.64  fof(f21,negated_conjecture,(
% 1.91/0.64    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.91/0.64    inference(negated_conjecture,[],[f20])).
% 1.91/0.64  fof(f20,conjecture,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.91/0.64  fof(f1180,plain,(
% 1.91/0.64    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.91/0.64    inference(backward_demodulation,[],[f1141,f1149])).
% 1.91/0.64  fof(f1149,plain,(
% 1.91/0.64    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_11)),
% 1.91/0.64    inference(forward_demodulation,[],[f1148,f60])).
% 1.91/0.64  fof(f60,plain,(
% 1.91/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.91/0.64    inference(cnf_transformation,[],[f9])).
% 1.91/0.64  fof(f9,axiom,(
% 1.91/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.91/0.64  fof(f1148,plain,(
% 1.91/0.64    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | (~spl5_4 | ~spl5_11)),
% 1.91/0.64    inference(resolution,[],[f1100,f64])).
% 1.91/0.64  fof(f64,plain,(
% 1.91/0.64    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 1.91/0.64    inference(cnf_transformation,[],[f26])).
% 1.91/0.64  fof(f26,plain,(
% 1.91/0.64    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.91/0.64    inference(ennf_transformation,[],[f11])).
% 1.91/0.64  fof(f11,axiom,(
% 1.91/0.64    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.91/0.64  fof(f1100,plain,(
% 1.91/0.64    v1_relat_1(k1_xboole_0) | (~spl5_4 | ~spl5_11)),
% 1.91/0.64    inference(backward_demodulation,[],[f143,f291])).
% 1.91/0.64  fof(f143,plain,(
% 1.91/0.64    v1_relat_1(sK3)),
% 1.91/0.64    inference(resolution,[],[f56,f80])).
% 1.91/0.64  fof(f80,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f34])).
% 1.91/0.64  fof(f34,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(ennf_transformation,[],[f13])).
% 1.91/0.64  fof(f13,axiom,(
% 1.91/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.91/0.64  fof(f56,plain,(
% 1.91/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.91/0.64    inference(cnf_transformation,[],[f46])).
% 1.91/0.64  fof(f1141,plain,(
% 1.91/0.64    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.91/0.64    inference(forward_demodulation,[],[f1140,f291])).
% 1.91/0.64  fof(f1140,plain,(
% 1.91/0.64    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_5)),
% 1.91/0.64    inference(forward_demodulation,[],[f417,f120])).
% 1.91/0.64  fof(f417,plain,(
% 1.91/0.64    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl5_2 | ~spl5_5)),
% 1.91/0.64    inference(backward_demodulation,[],[f196,f414])).
% 1.91/0.64  fof(f414,plain,(
% 1.91/0.64    k1_xboole_0 = sK2 | ~spl5_5),
% 1.91/0.64    inference(subsumption_resolution,[],[f413,f62])).
% 1.91/0.64  fof(f62,plain,(
% 1.91/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f2])).
% 1.91/0.64  fof(f2,axiom,(
% 1.91/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.91/0.64  fof(f413,plain,(
% 1.91/0.64    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl5_5),
% 1.91/0.64    inference(resolution,[],[f293,f73])).
% 1.91/0.64  fof(f73,plain,(
% 1.91/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f49])).
% 1.91/0.64  fof(f49,plain,(
% 1.91/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.91/0.64    inference(flattening,[],[f48])).
% 1.91/0.64  fof(f48,plain,(
% 1.91/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.91/0.64    inference(nnf_transformation,[],[f1])).
% 1.91/0.64  fof(f1,axiom,(
% 1.91/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.91/0.64  fof(f293,plain,(
% 1.91/0.64    r1_tarski(sK2,k1_xboole_0) | ~spl5_5),
% 1.91/0.64    inference(backward_demodulation,[],[f57,f125])).
% 1.91/0.64  fof(f57,plain,(
% 1.91/0.64    r1_tarski(sK2,sK0)),
% 1.91/0.64    inference(cnf_transformation,[],[f46])).
% 1.91/0.64  fof(f196,plain,(
% 1.91/0.64    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl5_2),
% 1.91/0.64    inference(backward_demodulation,[],[f112,f146])).
% 1.91/0.64  fof(f146,plain,(
% 1.91/0.64    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f139,f54])).
% 1.91/0.64  fof(f54,plain,(
% 1.91/0.64    v1_funct_1(sK3)),
% 1.91/0.64    inference(cnf_transformation,[],[f46])).
% 1.91/0.64  fof(f139,plain,(
% 1.91/0.64    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.91/0.64    inference(resolution,[],[f56,f91])).
% 1.91/0.64  fof(f91,plain,(
% 1.91/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f42])).
% 1.91/0.64  fof(f42,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.91/0.64    inference(flattening,[],[f41])).
% 1.91/0.64  fof(f41,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.91/0.64    inference(ennf_transformation,[],[f18])).
% 1.91/0.64  fof(f18,axiom,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.91/0.64  fof(f112,plain,(
% 1.91/0.64    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl5_2),
% 1.91/0.64    inference(avatar_component_clause,[],[f110])).
% 1.91/0.64  fof(f110,plain,(
% 1.91/0.64    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.91/0.64  fof(f1000,plain,(
% 1.91/0.64    spl5_15 | spl5_4),
% 1.91/0.64    inference(avatar_split_clause,[],[f317,f119,f266])).
% 1.91/0.64  fof(f266,plain,(
% 1.91/0.64    spl5_15 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.91/0.64  fof(f317,plain,(
% 1.91/0.64    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f310,f55])).
% 1.91/0.64  fof(f310,plain,(
% 1.91/0.64    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.91/0.64    inference(resolution,[],[f56,f83])).
% 1.91/0.64  fof(f83,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.91/0.64    inference(cnf_transformation,[],[f53])).
% 1.91/0.64  fof(f53,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(nnf_transformation,[],[f38])).
% 1.91/0.64  fof(f38,plain,(
% 1.91/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(flattening,[],[f37])).
% 1.91/0.64  fof(f37,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(ennf_transformation,[],[f16])).
% 1.91/0.64  fof(f16,axiom,(
% 1.91/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.91/0.64  fof(f944,plain,(
% 1.91/0.64    spl5_3 | ~spl5_15),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f943])).
% 1.91/0.64  fof(f943,plain,(
% 1.91/0.64    $false | (spl5_3 | ~spl5_15)),
% 1.91/0.64    inference(subsumption_resolution,[],[f933,f222])).
% 1.91/0.64  fof(f222,plain,(
% 1.91/0.64    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f219,f154])).
% 1.91/0.64  fof(f154,plain,(
% 1.91/0.64    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.91/0.64    inference(resolution,[],[f153,f103])).
% 1.91/0.64  fof(f103,plain,(
% 1.91/0.64    ( ! [X2,X0] : (sP4(X2) | v1_relat_1(k7_relat_1(X2,X0))) )),
% 1.91/0.64    inference(cnf_transformation,[],[f103_D])).
% 1.91/0.64  fof(f103_D,plain,(
% 1.91/0.64    ( ! [X2] : (( ! [X0] : v1_relat_1(k7_relat_1(X2,X0)) ) <=> ~sP4(X2)) )),
% 1.91/0.64    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 1.91/0.64  fof(f153,plain,(
% 1.91/0.64    ~sP4(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f151,f143])).
% 1.91/0.64  fof(f151,plain,(
% 1.91/0.64    ~v1_relat_1(sK3) | ~sP4(sK3)),
% 1.91/0.64    inference(resolution,[],[f141,f104])).
% 1.91/0.64  fof(f104,plain,(
% 1.91/0.64    ( ! [X2,X1] : (~v5_relat_1(X2,X1) | ~v1_relat_1(X2) | ~sP4(X2)) )),
% 1.91/0.64    inference(general_splitting,[],[f89,f103_D])).
% 1.91/0.64  fof(f89,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f40])).
% 1.91/0.64  fof(f40,plain,(
% 1.91/0.64    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 1.91/0.64    inference(flattening,[],[f39])).
% 1.91/0.64  fof(f39,plain,(
% 1.91/0.64    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 1.91/0.64    inference(ennf_transformation,[],[f12])).
% 1.91/0.64  fof(f12,axiom,(
% 1.91/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).
% 1.91/0.64  fof(f141,plain,(
% 1.91/0.64    v5_relat_1(sK3,sK1)),
% 1.91/0.64    inference(resolution,[],[f56,f82])).
% 1.91/0.64  fof(f82,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f36])).
% 1.91/0.64  fof(f36,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(ennf_transformation,[],[f22])).
% 1.91/0.64  fof(f22,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.91/0.64    inference(pure_predicate_removal,[],[f14])).
% 1.91/0.64  fof(f14,axiom,(
% 1.91/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.91/0.64  fof(f219,plain,(
% 1.91/0.64    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.91/0.64    inference(resolution,[],[f211,f66])).
% 1.91/0.64  fof(f66,plain,(
% 1.91/0.64    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f47])).
% 1.91/0.64  fof(f47,plain,(
% 1.91/0.64    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.91/0.64    inference(nnf_transformation,[],[f29])).
% 1.91/0.64  fof(f29,plain,(
% 1.91/0.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.91/0.64    inference(ennf_transformation,[],[f7])).
% 1.91/0.64  fof(f7,axiom,(
% 1.91/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.91/0.64  fof(f211,plain,(
% 1.91/0.64    ( ! [X5] : (v5_relat_1(k7_relat_1(sK3,X5),sK1)) )),
% 1.91/0.64    inference(resolution,[],[f199,f82])).
% 1.91/0.64  fof(f199,plain,(
% 1.91/0.64    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f198,f54])).
% 1.91/0.64  fof(f198,plain,(
% 1.91/0.64    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f197,f56])).
% 1.91/0.64  fof(f197,plain,(
% 1.91/0.64    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.91/0.64    inference(superposition,[],[f93,f146])).
% 1.91/0.64  fof(f93,plain,(
% 1.91/0.64    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f44])).
% 1.91/0.64  fof(f44,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.91/0.64    inference(flattening,[],[f43])).
% 1.91/0.64  fof(f43,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.91/0.64    inference(ennf_transformation,[],[f17])).
% 1.91/0.64  fof(f17,axiom,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.91/0.64  fof(f933,plain,(
% 1.91/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl5_3 | ~spl5_15)),
% 1.91/0.64    inference(resolution,[],[f601,f697])).
% 1.91/0.64  fof(f697,plain,(
% 1.91/0.64    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_3),
% 1.91/0.64    inference(forward_demodulation,[],[f116,f146])).
% 1.91/0.64  fof(f116,plain,(
% 1.91/0.64    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_3),
% 1.91/0.64    inference(avatar_component_clause,[],[f114])).
% 1.91/0.64  fof(f114,plain,(
% 1.91/0.64    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.91/0.64  fof(f601,plain,(
% 1.91/0.64    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl5_15),
% 1.91/0.64    inference(subsumption_resolution,[],[f600,f154])).
% 1.91/0.64  fof(f600,plain,(
% 1.91/0.64    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl5_15),
% 1.91/0.64    inference(subsumption_resolution,[],[f596,f195])).
% 1.91/0.64  fof(f195,plain,(
% 1.91/0.64    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.91/0.64    inference(backward_demodulation,[],[f145,f146])).
% 1.91/0.64  fof(f145,plain,(
% 1.91/0.64    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f138,f54])).
% 1.91/0.64  fof(f138,plain,(
% 1.91/0.64    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.91/0.64    inference(resolution,[],[f56,f92])).
% 1.91/0.64  fof(f92,plain,(
% 1.91/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f44])).
% 1.91/0.64  fof(f596,plain,(
% 1.91/0.64    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl5_15),
% 1.91/0.64    inference(superposition,[],[f70,f588])).
% 1.91/0.64  fof(f588,plain,(
% 1.91/0.64    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl5_15),
% 1.91/0.64    inference(resolution,[],[f358,f57])).
% 1.91/0.64  fof(f358,plain,(
% 1.91/0.64    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl5_15),
% 1.91/0.64    inference(subsumption_resolution,[],[f351,f143])).
% 1.91/0.64  fof(f351,plain,(
% 1.91/0.64    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | ~spl5_15),
% 1.91/0.64    inference(superposition,[],[f65,f348])).
% 1.91/0.64  fof(f348,plain,(
% 1.91/0.64    sK0 = k1_relat_1(sK3) | ~spl5_15),
% 1.91/0.64    inference(forward_demodulation,[],[f142,f268])).
% 1.91/0.64  fof(f268,plain,(
% 1.91/0.64    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_15),
% 1.91/0.64    inference(avatar_component_clause,[],[f266])).
% 1.91/0.64  fof(f142,plain,(
% 1.91/0.64    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.91/0.64    inference(resolution,[],[f56,f81])).
% 1.91/0.64  fof(f81,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f35])).
% 1.91/0.64  fof(f35,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(ennf_transformation,[],[f15])).
% 1.91/0.64  fof(f15,axiom,(
% 1.91/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.91/0.64  fof(f65,plain,(
% 1.91/0.64    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f28])).
% 1.91/0.64  fof(f28,plain,(
% 1.91/0.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.91/0.64    inference(flattening,[],[f27])).
% 1.91/0.64  fof(f27,plain,(
% 1.91/0.64    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.91/0.64    inference(ennf_transformation,[],[f10])).
% 1.91/0.64  fof(f10,axiom,(
% 1.91/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.91/0.64  fof(f70,plain,(
% 1.91/0.64    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f31])).
% 1.91/0.64  fof(f31,plain,(
% 1.91/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.91/0.64    inference(flattening,[],[f30])).
% 1.91/0.64  fof(f30,plain,(
% 1.91/0.64    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.91/0.64    inference(ennf_transformation,[],[f19])).
% 1.91/0.64  fof(f19,axiom,(
% 1.91/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.91/0.64  fof(f696,plain,(
% 1.91/0.64    spl5_2 | ~spl5_15),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f695])).
% 1.91/0.64  fof(f695,plain,(
% 1.91/0.64    $false | (spl5_2 | ~spl5_15)),
% 1.91/0.64    inference(subsumption_resolution,[],[f694,f196])).
% 1.91/0.64  fof(f694,plain,(
% 1.91/0.64    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl5_15),
% 1.91/0.64    inference(resolution,[],[f599,f222])).
% 1.91/0.64  fof(f599,plain,(
% 1.91/0.64    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)) ) | ~spl5_15),
% 1.91/0.64    inference(subsumption_resolution,[],[f598,f154])).
% 1.91/0.64  fof(f598,plain,(
% 1.91/0.64    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl5_15),
% 1.91/0.64    inference(subsumption_resolution,[],[f595,f195])).
% 1.91/0.64  fof(f595,plain,(
% 1.91/0.64    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl5_15),
% 1.91/0.64    inference(superposition,[],[f69,f588])).
% 1.91/0.64  fof(f69,plain,(
% 1.91/0.64    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f31])).
% 1.91/0.64  fof(f505,plain,(
% 1.91/0.64    ~spl5_6 | spl5_7),
% 1.91/0.64    inference(avatar_split_clause,[],[f504,f134,f130])).
% 1.91/0.64  fof(f130,plain,(
% 1.91/0.64    spl5_6 <=> r1_tarski(sK0,sK2)),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.91/0.64  fof(f134,plain,(
% 1.91/0.64    spl5_7 <=> sK0 = sK2),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.91/0.64  fof(f504,plain,(
% 1.91/0.64    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 1.91/0.64    inference(resolution,[],[f57,f73])).
% 1.91/0.64  fof(f502,plain,(
% 1.91/0.64    spl5_3 | ~spl5_7),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f501])).
% 1.91/0.64  fof(f501,plain,(
% 1.91/0.64    $false | (spl5_3 | ~spl5_7)),
% 1.91/0.64    inference(subsumption_resolution,[],[f500,f54])).
% 1.91/0.64  fof(f500,plain,(
% 1.91/0.64    ~v1_funct_1(sK3) | (spl5_3 | ~spl5_7)),
% 1.91/0.64    inference(subsumption_resolution,[],[f498,f56])).
% 1.91/0.64  fof(f498,plain,(
% 1.91/0.64    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (spl5_3 | ~spl5_7)),
% 1.91/0.64    inference(resolution,[],[f495,f93])).
% 1.91/0.64  fof(f495,plain,(
% 1.91/0.64    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl5_3 | ~spl5_7)),
% 1.91/0.64    inference(forward_demodulation,[],[f116,f136])).
% 1.91/0.64  fof(f136,plain,(
% 1.91/0.64    sK0 = sK2 | ~spl5_7),
% 1.91/0.64    inference(avatar_component_clause,[],[f134])).
% 1.91/0.64  fof(f484,plain,(
% 1.91/0.64    ~spl5_10 | spl5_11),
% 1.91/0.64    inference(avatar_split_clause,[],[f483,f175,f171])).
% 1.91/0.64  fof(f171,plain,(
% 1.91/0.64    spl5_10 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.91/0.64  fof(f483,plain,(
% 1.91/0.64    sK3 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.91/0.64    inference(resolution,[],[f144,f73])).
% 1.91/0.64  fof(f144,plain,(
% 1.91/0.64    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.91/0.64    inference(resolution,[],[f56,f74])).
% 1.91/0.64  fof(f74,plain,(
% 1.91/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f50,plain,(
% 1.91/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.91/0.64    inference(nnf_transformation,[],[f5])).
% 1.91/0.64  fof(f5,axiom,(
% 1.91/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.91/0.64  fof(f297,plain,(
% 1.91/0.64    ~spl5_5 | spl5_6),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f296])).
% 1.91/0.64  fof(f296,plain,(
% 1.91/0.64    $false | (~spl5_5 | spl5_6)),
% 1.91/0.64    inference(subsumption_resolution,[],[f295,f62])).
% 1.91/0.64  fof(f295,plain,(
% 1.91/0.64    ~r1_tarski(k1_xboole_0,sK2) | (~spl5_5 | spl5_6)),
% 1.91/0.64    inference(backward_demodulation,[],[f132,f125])).
% 1.91/0.64  fof(f132,plain,(
% 1.91/0.64    ~r1_tarski(sK0,sK2) | spl5_6),
% 1.91/0.64    inference(avatar_component_clause,[],[f130])).
% 1.91/0.64  fof(f288,plain,(
% 1.91/0.64    ~spl5_4 | spl5_10),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f287])).
% 1.91/0.64  fof(f287,plain,(
% 1.91/0.64    $false | (~spl5_4 | spl5_10)),
% 1.91/0.64    inference(subsumption_resolution,[],[f286,f62])).
% 1.91/0.64  fof(f286,plain,(
% 1.91/0.64    ~r1_tarski(k1_xboole_0,sK3) | (~spl5_4 | spl5_10)),
% 1.91/0.64    inference(forward_demodulation,[],[f277,f96])).
% 1.91/0.64  fof(f277,plain,(
% 1.91/0.64    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | (~spl5_4 | spl5_10)),
% 1.91/0.64    inference(backward_demodulation,[],[f173,f120])).
% 1.91/0.64  fof(f173,plain,(
% 1.91/0.64    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl5_10),
% 1.91/0.64    inference(avatar_component_clause,[],[f171])).
% 1.91/0.64  fof(f180,plain,(
% 1.91/0.64    spl5_1),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f179])).
% 1.91/0.64  fof(f179,plain,(
% 1.91/0.64    $false | spl5_1),
% 1.91/0.64    inference(resolution,[],[f145,f108])).
% 1.91/0.64  fof(f108,plain,(
% 1.91/0.64    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl5_1),
% 1.91/0.64    inference(avatar_component_clause,[],[f106])).
% 1.91/0.64  fof(f106,plain,(
% 1.91/0.64    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.91/0.64  fof(f126,plain,(
% 1.91/0.64    ~spl5_4 | spl5_5),
% 1.91/0.64    inference(avatar_split_clause,[],[f58,f123,f119])).
% 1.91/0.64  fof(f58,plain,(
% 1.91/0.64    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.91/0.64    inference(cnf_transformation,[],[f46])).
% 1.91/0.64  fof(f117,plain,(
% 1.91/0.64    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.91/0.64    inference(avatar_split_clause,[],[f59,f114,f110,f106])).
% 1.91/0.64  fof(f59,plain,(
% 1.91/0.64    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.91/0.64    inference(cnf_transformation,[],[f46])).
% 1.91/0.64  % SZS output end Proof for theBenchmark
% 1.91/0.64  % (12372)------------------------------
% 1.91/0.64  % (12372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.64  % (12372)Termination reason: Refutation
% 1.91/0.64  
% 1.91/0.64  % (12372)Memory used [KB]: 11129
% 1.91/0.64  % (12372)Time elapsed: 0.187 s
% 1.91/0.64  % (12372)------------------------------
% 1.91/0.64  % (12372)------------------------------
% 1.91/0.64  % (12370)Success in time 0.281 s
%------------------------------------------------------------------------------
