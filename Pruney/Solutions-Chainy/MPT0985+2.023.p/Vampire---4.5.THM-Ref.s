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
% DateTime   : Thu Dec  3 13:02:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 713 expanded)
%              Number of leaves         :   44 ( 246 expanded)
%              Depth                    :   14
%              Number of atoms          :  759 (3284 expanded)
%              Number of equality atoms :  106 ( 593 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1012,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f129,f136,f141,f147,f173,f176,f323,f366,f369,f379,f411,f461,f470,f473,f496,f500,f546,f634,f680,f685,f704,f745,f821,f921,f923,f953,f973,f1003,f1011])).

fof(f1011,plain,
    ( spl6_2
    | ~ spl6_10
    | ~ spl6_26
    | ~ spl6_79 ),
    inference(avatar_contradiction_clause,[],[f1010])).

fof(f1010,plain,
    ( $false
    | spl6_2
    | ~ spl6_10
    | ~ spl6_26
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f957,f969])).

fof(f969,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f968])).

fof(f968,plain,
    ( spl6_79
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f957,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl6_2
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f956,f286])).

fof(f286,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl6_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f956,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl6_2
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f117,f161])).

fof(f161,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f117,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1003,plain,
    ( ~ spl6_3
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26
    | spl6_80 ),
    inference(avatar_contradiction_clause,[],[f1002])).

fof(f1002,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26
    | spl6_80 ),
    inference(subsumption_resolution,[],[f972,f976])).

fof(f976,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f963,f775])).

fof(f775,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f377,f286])).

fof(f377,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f228,f161])).

fof(f228,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f135,f227])).

fof(f227,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f150,f66])).

fof(f66,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f46])).

fof(f46,plain,
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

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f150,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f64,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f135,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_6
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f963,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(resolution,[],[f955,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f955,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f954,f286])).

fof(f954,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f368,f161])).

fof(f368,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f972,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl6_80 ),
    inference(avatar_component_clause,[],[f971])).

fof(f971,plain,
    ( spl6_80
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f973,plain,
    ( spl6_79
    | ~ spl6_80
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f959,f285,f160,f119,f971,f968])).

fof(f959,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(resolution,[],[f955,f110])).

fof(f110,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f953,plain,
    ( spl6_3
    | ~ spl6_10
    | ~ spl6_26
    | ~ spl6_74 ),
    inference(avatar_contradiction_clause,[],[f952])).

fof(f952,plain,
    ( $false
    | spl6_3
    | ~ spl6_10
    | ~ spl6_26
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f920,f951])).

fof(f951,plain,
    ( ~ v1_xboole_0(k2_funct_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(resolution,[],[f838,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f838,plain,
    ( r2_hidden(sK4(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)),k2_funct_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(resolution,[],[f804,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f804,plain,
    ( ~ r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl6_3
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(resolution,[],[f803,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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

fof(f803,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_3
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f763,f286])).

fof(f763,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_3
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f120,f161])).

fof(f120,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f920,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f919])).

fof(f919,plain,
    ( spl6_74
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f923,plain,(
    spl6_40 ),
    inference(avatar_contradiction_clause,[],[f922])).

fof(f922,plain,
    ( $false
    | spl6_40 ),
    inference(subsumption_resolution,[],[f68,f441])).

fof(f441,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl6_40
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f921,plain,
    ( ~ spl6_40
    | spl6_74
    | ~ spl6_67 ),
    inference(avatar_split_clause,[],[f905,f819,f919,f440])).

fof(f819,plain,
    ( spl6_67
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f905,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_67 ),
    inference(resolution,[],[f820,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f820,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0))))
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f819])).

fof(f821,plain,
    ( ~ spl6_36
    | ~ spl6_52
    | spl6_67
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f817,f404,f285,f160,f134,f819,f615,f391])).

fof(f391,plain,
    ( spl6_36
  <=> v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f615,plain,
    ( spl6_52
  <=> v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f404,plain,
    ( spl6_39
  <=> k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f817,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0))))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f811,f405])).

fof(f405,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f404])).

fof(f811,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(superposition,[],[f74,f775])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f745,plain,
    ( spl6_3
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_63 ),
    inference(avatar_contradiction_clause,[],[f734])).

fof(f734,plain,
    ( $false
    | spl6_3
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f706,f684])).

fof(f684,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f683])).

fof(f683,plain,
    ( spl6_63
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f706,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl6_3
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f705,f161])).

fof(f705,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | spl6_3
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f120,f289])).

fof(f289,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl6_27
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f704,plain,
    ( spl6_2
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_62 ),
    inference(avatar_contradiction_clause,[],[f703])).

fof(f703,plain,
    ( $false
    | spl6_2
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f552,f679])).

fof(f679,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f678])).

fof(f678,plain,
    ( spl6_62
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f552,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(backward_demodulation,[],[f373,f289])).

fof(f373,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl6_2
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f117,f161])).

fof(f685,plain,
    ( ~ spl6_5
    | ~ spl6_1
    | spl6_63
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f681,f456,f288,f160,f139,f134,f683,f113,f127])).

fof(f127,plain,
    ( spl6_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f113,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f139,plain,
    ( spl6_7
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f456,plain,
    ( spl6_41
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f681,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f671,f377])).

fof(f671,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_41 ),
    inference(superposition,[],[f74,f659])).

fof(f659,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_41 ),
    inference(backward_demodulation,[],[f140,f657])).

fof(f657,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f656,f457])).

fof(f457,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f456])).

fof(f656,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f655,f289])).

fof(f655,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f151,f161])).

fof(f151,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f64,f97])).

fof(f140,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f680,plain,
    ( ~ spl6_5
    | ~ spl6_1
    | spl6_62
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f676,f456,f288,f160,f139,f134,f678,f113,f127])).

fof(f676,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f670,f377])).

fof(f670,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_41 ),
    inference(superposition,[],[f73,f659])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f634,plain,
    ( ~ spl6_35
    | ~ spl6_37
    | spl6_52 ),
    inference(avatar_split_clause,[],[f632,f615,f397,f388])).

fof(f388,plain,
    ( spl6_35
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f397,plain,
    ( spl6_37
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f632,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl6_52 ),
    inference(resolution,[],[f616,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f616,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | spl6_52 ),
    inference(avatar_component_clause,[],[f615])).

fof(f546,plain,
    ( spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f538,f160,f291,f288,f285])).

fof(f291,plain,
    ( spl6_28
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f538,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_10 ),
    inference(resolution,[],[f371,f109])).

fof(f109,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f371,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f64,f161])).

fof(f500,plain,
    ( ~ spl6_35
    | ~ spl6_37
    | spl6_39
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f498,f285,f404,f397,f388])).

fof(f498,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_26 ),
    inference(resolution,[],[f485,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f485,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f65,f286])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f496,plain,
    ( ~ spl6_35
    | spl6_36
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f495,f285,f391,f388])).

fof(f495,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_26 ),
    inference(resolution,[],[f484,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f484,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f62,f286])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f473,plain,(
    spl6_37 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | spl6_37 ),
    inference(subsumption_resolution,[],[f68,f471])).

fof(f471,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_37 ),
    inference(resolution,[],[f398,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f398,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl6_37 ),
    inference(avatar_component_clause,[],[f397])).

fof(f470,plain,
    ( ~ spl6_10
    | ~ spl6_27
    | spl6_42 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_27
    | spl6_42 ),
    inference(subsumption_resolution,[],[f432,f460])).

fof(f460,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl6_42
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f432,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(backward_demodulation,[],[f370,f289])).

fof(f370,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f63,f161])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f461,plain,
    ( spl6_41
    | ~ spl6_42
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f445,f288,f160,f459,f456])).

fof(f445,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(resolution,[],[f433,f111])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f433,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(backward_demodulation,[],[f371,f289])).

fof(f411,plain,
    ( ~ spl6_26
    | spl6_35 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl6_26
    | spl6_35 ),
    inference(subsumption_resolution,[],[f383,f389])).

fof(f389,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f388])).

fof(f383,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f152,f286])).

fof(f152,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f64,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f379,plain,
    ( ~ spl6_10
    | spl6_28 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl6_10
    | spl6_28 ),
    inference(subsumption_resolution,[],[f292,f370])).

fof(f292,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f291])).

fof(f369,plain,
    ( ~ spl6_5
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f367,f157,f139,f134,f119,f113,f127])).

fof(f157,plain,
    ( spl6_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f367,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f359,f228])).

fof(f359,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(superposition,[],[f74,f350])).

fof(f350,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f140,f348])).

fof(f348,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f151,f158])).

fof(f158,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f366,plain,
    ( ~ spl6_5
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f364,f157,f139,f134,f116,f113,f127])).

fof(f364,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f358,f228])).

fof(f358,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(superposition,[],[f73,f350])).

fof(f323,plain,
    ( spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f322,f160,f157])).

fof(f322,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f63,f315])).

fof(f315,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f64,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f176,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f62,f146])).

fof(f146,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f173,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f125,f152])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f147,plain,
    ( ~ spl6_4
    | ~ spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f142,f113,f145,f124])).

fof(f142,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(resolution,[],[f114,f76])).

fof(f114,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f141,plain,
    ( ~ spl6_4
    | spl6_7 ),
    inference(avatar_split_clause,[],[f137,f139,f124])).

fof(f137,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(global_subsumption,[],[f62,f131])).

fof(f131,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f78])).

fof(f136,plain,
    ( ~ spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f132,f134,f124])).

fof(f132,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(global_subsumption,[],[f62,f130])).

fof(f130,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f129,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f122,f127,f124])).

fof(f122,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f75])).

fof(f121,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f67,f119,f116,f113])).

fof(f67,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:54:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (2002)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.48  % (1994)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (1981)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (1990)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (1997)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (1979)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (1983)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (1986)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (1980)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1982)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (1981)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1012,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f121,f129,f136,f141,f147,f173,f176,f323,f366,f369,f379,f411,f461,f470,f473,f496,f500,f546,f634,f680,f685,f704,f745,f821,f921,f923,f953,f973,f1003,f1011])).
% 0.21/0.54  fof(f1011,plain,(
% 0.21/0.54    spl6_2 | ~spl6_10 | ~spl6_26 | ~spl6_79),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1010])).
% 0.21/0.54  fof(f1010,plain,(
% 0.21/0.54    $false | (spl6_2 | ~spl6_10 | ~spl6_26 | ~spl6_79)),
% 0.21/0.54    inference(subsumption_resolution,[],[f957,f969])).
% 0.21/0.54  fof(f969,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~spl6_79),
% 0.21/0.54    inference(avatar_component_clause,[],[f968])).
% 0.21/0.54  fof(f968,plain,(
% 0.21/0.54    spl6_79 <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 0.21/0.54  fof(f957,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl6_2 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(forward_demodulation,[],[f956,f286])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~spl6_26),
% 0.21/0.54    inference(avatar_component_clause,[],[f285])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    spl6_26 <=> k1_xboole_0 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.54  fof(f956,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl6_2 | ~spl6_10)),
% 0.21/0.54    inference(forward_demodulation,[],[f117,f161])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl6_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    spl6_10 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl6_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl6_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.54  fof(f1003,plain,(
% 0.21/0.54    ~spl6_3 | ~spl6_6 | ~spl6_10 | ~spl6_26 | spl6_80),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1002])).
% 0.21/0.54  fof(f1002,plain,(
% 0.21/0.54    $false | (~spl6_3 | ~spl6_6 | ~spl6_10 | ~spl6_26 | spl6_80)),
% 0.21/0.54    inference(subsumption_resolution,[],[f972,f976])).
% 0.21/0.54  fof(f976,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (~spl6_3 | ~spl6_6 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(forward_demodulation,[],[f963,f775])).
% 0.21/0.54  fof(f775,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl6_6 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(backward_demodulation,[],[f377,f286])).
% 0.21/0.54  fof(f377,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | (~spl6_6 | ~spl6_10)),
% 0.21/0.54    inference(backward_demodulation,[],[f228,f161])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl6_6),
% 0.21/0.54    inference(backward_demodulation,[],[f135,f227])).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f150,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f20])).
% 0.21/0.54  fof(f20,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f64,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl6_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl6_6 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.54  fof(f963,plain,(
% 0.21/0.54    k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (~spl6_3 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(resolution,[],[f955,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f955,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl6_3 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(forward_demodulation,[],[f954,f286])).
% 0.21/0.54  fof(f954,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl6_3 | ~spl6_10)),
% 0.21/0.54    inference(forward_demodulation,[],[f368,f161])).
% 0.21/0.54  fof(f368,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl6_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.54  fof(f972,plain,(
% 0.21/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | spl6_80),
% 0.21/0.54    inference(avatar_component_clause,[],[f971])).
% 0.21/0.54  fof(f971,plain,(
% 0.21/0.54    spl6_80 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 0.21/0.54  fof(f973,plain,(
% 0.21/0.54    spl6_79 | ~spl6_80 | ~spl6_3 | ~spl6_10 | ~spl6_26),
% 0.21/0.54    inference(avatar_split_clause,[],[f959,f285,f160,f119,f971,f968])).
% 0.21/0.54  fof(f959,plain,(
% 0.21/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (~spl6_3 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(resolution,[],[f955,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f953,plain,(
% 0.21/0.54    spl6_3 | ~spl6_10 | ~spl6_26 | ~spl6_74),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f952])).
% 0.21/0.54  fof(f952,plain,(
% 0.21/0.54    $false | (spl6_3 | ~spl6_10 | ~spl6_26 | ~spl6_74)),
% 0.21/0.54    inference(subsumption_resolution,[],[f920,f951])).
% 0.21/0.54  fof(f951,plain,(
% 0.21/0.54    ~v1_xboole_0(k2_funct_1(k1_xboole_0)) | (spl6_3 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(resolution,[],[f838,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(rectify,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  fof(f838,plain,(
% 0.21/0.54    r2_hidden(sK4(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)),k2_funct_1(k1_xboole_0)) | (spl6_3 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(resolution,[],[f804,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f804,plain,(
% 0.21/0.54    ~r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) | (spl6_3 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(resolution,[],[f803,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f803,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl6_3 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(forward_demodulation,[],[f763,f286])).
% 0.21/0.54  fof(f763,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl6_3 | ~spl6_10)),
% 0.21/0.54    inference(forward_demodulation,[],[f120,f161])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f119])).
% 0.21/0.54  fof(f920,plain,(
% 0.21/0.54    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~spl6_74),
% 0.21/0.54    inference(avatar_component_clause,[],[f919])).
% 0.21/0.54  fof(f919,plain,(
% 0.21/0.54    spl6_74 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 0.21/0.54  fof(f923,plain,(
% 0.21/0.54    spl6_40),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f922])).
% 0.21/0.54  fof(f922,plain,(
% 0.21/0.54    $false | spl6_40),
% 0.21/0.54    inference(subsumption_resolution,[],[f68,f441])).
% 0.21/0.54  fof(f441,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | spl6_40),
% 0.21/0.54    inference(avatar_component_clause,[],[f440])).
% 0.21/0.54  fof(f440,plain,(
% 0.21/0.54    spl6_40 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f921,plain,(
% 0.21/0.54    ~spl6_40 | spl6_74 | ~spl6_67),
% 0.21/0.54    inference(avatar_split_clause,[],[f905,f819,f919,f440])).
% 0.21/0.54  fof(f819,plain,(
% 0.21/0.54    spl6_67 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 0.21/0.54  fof(f905,plain,(
% 0.21/0.54    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | ~spl6_67),
% 0.21/0.54    inference(resolution,[],[f820,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.54  fof(f820,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) | ~spl6_67),
% 0.21/0.54    inference(avatar_component_clause,[],[f819])).
% 0.21/0.54  fof(f821,plain,(
% 0.21/0.54    ~spl6_36 | ~spl6_52 | spl6_67 | ~spl6_6 | ~spl6_10 | ~spl6_26 | ~spl6_39),
% 0.21/0.54    inference(avatar_split_clause,[],[f817,f404,f285,f160,f134,f819,f615,f391])).
% 0.21/0.54  fof(f391,plain,(
% 0.21/0.54    spl6_36 <=> v1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.54  fof(f615,plain,(
% 0.21/0.54    spl6_52 <=> v1_funct_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.21/0.54  fof(f404,plain,(
% 0.21/0.54    spl6_39 <=> k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.54  fof(f817,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl6_6 | ~spl6_10 | ~spl6_26 | ~spl6_39)),
% 0.21/0.54    inference(forward_demodulation,[],[f811,f405])).
% 0.21/0.54  fof(f405,plain,(
% 0.21/0.54    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~spl6_39),
% 0.21/0.54    inference(avatar_component_clause,[],[f404])).
% 0.21/0.54  fof(f811,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl6_6 | ~spl6_10 | ~spl6_26)),
% 0.21/0.54    inference(superposition,[],[f74,f775])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.54  fof(f745,plain,(
% 0.21/0.54    spl6_3 | ~spl6_10 | ~spl6_27 | ~spl6_63),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f734])).
% 0.21/0.54  fof(f734,plain,(
% 0.21/0.54    $false | (spl6_3 | ~spl6_10 | ~spl6_27 | ~spl6_63)),
% 0.21/0.54    inference(subsumption_resolution,[],[f706,f684])).
% 0.21/0.54  fof(f684,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_63),
% 0.21/0.54    inference(avatar_component_clause,[],[f683])).
% 0.21/0.54  fof(f683,plain,(
% 0.21/0.54    spl6_63 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.21/0.54  fof(f706,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl6_3 | ~spl6_10 | ~spl6_27)),
% 0.21/0.54    inference(forward_demodulation,[],[f705,f161])).
% 0.21/0.54  fof(f705,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (spl6_3 | ~spl6_27)),
% 0.21/0.54    inference(forward_demodulation,[],[f120,f289])).
% 0.21/0.54  fof(f289,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl6_27),
% 0.21/0.54    inference(avatar_component_clause,[],[f288])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    spl6_27 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.54  fof(f704,plain,(
% 0.21/0.54    spl6_2 | ~spl6_10 | ~spl6_27 | ~spl6_62),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f703])).
% 0.21/0.54  fof(f703,plain,(
% 0.21/0.54    $false | (spl6_2 | ~spl6_10 | ~spl6_27 | ~spl6_62)),
% 0.21/0.54    inference(subsumption_resolution,[],[f552,f679])).
% 0.21/0.54  fof(f679,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | ~spl6_62),
% 0.21/0.54    inference(avatar_component_clause,[],[f678])).
% 0.21/0.54  fof(f678,plain,(
% 0.21/0.54    spl6_62 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.21/0.54  fof(f552,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_10 | ~spl6_27)),
% 0.21/0.54    inference(backward_demodulation,[],[f373,f289])).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl6_2 | ~spl6_10)),
% 0.21/0.54    inference(backward_demodulation,[],[f117,f161])).
% 0.21/0.54  fof(f685,plain,(
% 0.21/0.54    ~spl6_5 | ~spl6_1 | spl6_63 | ~spl6_6 | ~spl6_7 | ~spl6_10 | ~spl6_27 | ~spl6_41),
% 0.21/0.54    inference(avatar_split_clause,[],[f681,f456,f288,f160,f139,f134,f683,f113,f127])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    spl6_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    spl6_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    spl6_7 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.54  fof(f456,plain,(
% 0.21/0.54    spl6_41 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.54  fof(f681,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_6 | ~spl6_7 | ~spl6_10 | ~spl6_27 | ~spl6_41)),
% 0.21/0.54    inference(forward_demodulation,[],[f671,f377])).
% 0.21/0.54  fof(f671,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_7 | ~spl6_10 | ~spl6_27 | ~spl6_41)),
% 0.21/0.54    inference(superposition,[],[f74,f659])).
% 0.21/0.54  fof(f659,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) | (~spl6_7 | ~spl6_10 | ~spl6_27 | ~spl6_41)),
% 0.21/0.54    inference(backward_demodulation,[],[f140,f657])).
% 0.21/0.54  fof(f657,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(sK2) | (~spl6_10 | ~spl6_27 | ~spl6_41)),
% 0.21/0.54    inference(forward_demodulation,[],[f656,f457])).
% 0.21/0.54  fof(f457,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl6_41),
% 0.21/0.54    inference(avatar_component_clause,[],[f456])).
% 0.21/0.54  fof(f656,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_10 | ~spl6_27)),
% 0.21/0.54    inference(forward_demodulation,[],[f655,f289])).
% 0.21/0.54  fof(f655,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl6_10),
% 0.21/0.54    inference(forward_demodulation,[],[f151,f161])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f64,f97])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl6_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f139])).
% 0.21/0.54  fof(f680,plain,(
% 0.21/0.54    ~spl6_5 | ~spl6_1 | spl6_62 | ~spl6_6 | ~spl6_7 | ~spl6_10 | ~spl6_27 | ~spl6_41),
% 0.21/0.54    inference(avatar_split_clause,[],[f676,f456,f288,f160,f139,f134,f678,f113,f127])).
% 0.21/0.54  fof(f676,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_6 | ~spl6_7 | ~spl6_10 | ~spl6_27 | ~spl6_41)),
% 0.21/0.54    inference(forward_demodulation,[],[f670,f377])).
% 0.21/0.54  fof(f670,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_xboole_0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_7 | ~spl6_10 | ~spl6_27 | ~spl6_41)),
% 0.21/0.54    inference(superposition,[],[f73,f659])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f634,plain,(
% 0.21/0.54    ~spl6_35 | ~spl6_37 | spl6_52),
% 0.21/0.54    inference(avatar_split_clause,[],[f632,f615,f397,f388])).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    spl6_35 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.54  fof(f397,plain,(
% 0.21/0.54    spl6_37 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.54  fof(f632,plain,(
% 0.21/0.54    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | spl6_52),
% 0.21/0.54    inference(resolution,[],[f616,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.54  fof(f616,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | spl6_52),
% 0.21/0.54    inference(avatar_component_clause,[],[f615])).
% 0.21/0.54  fof(f546,plain,(
% 0.21/0.54    spl6_26 | spl6_27 | ~spl6_28 | ~spl6_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f538,f160,f291,f288,f285])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    spl6_28 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.54  fof(f538,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl6_10),
% 0.21/0.54    inference(resolution,[],[f371,f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f61])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_10),
% 0.21/0.54    inference(backward_demodulation,[],[f64,f161])).
% 0.21/0.54  fof(f500,plain,(
% 0.21/0.54    ~spl6_35 | ~spl6_37 | spl6_39 | ~spl6_26),
% 0.21/0.54    inference(avatar_split_clause,[],[f498,f285,f404,f397,f388])).
% 0.21/0.54  fof(f498,plain,(
% 0.21/0.54    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl6_26),
% 0.21/0.54    inference(resolution,[],[f485,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.54  fof(f485,plain,(
% 0.21/0.54    v2_funct_1(k1_xboole_0) | ~spl6_26),
% 0.21/0.54    inference(backward_demodulation,[],[f65,f286])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    v2_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f496,plain,(
% 0.21/0.54    ~spl6_35 | spl6_36 | ~spl6_26),
% 0.21/0.54    inference(avatar_split_clause,[],[f495,f285,f391,f388])).
% 0.21/0.54  fof(f495,plain,(
% 0.21/0.54    v1_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~spl6_26),
% 0.21/0.54    inference(resolution,[],[f484,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f484,plain,(
% 0.21/0.54    v1_funct_1(k1_xboole_0) | ~spl6_26),
% 0.21/0.54    inference(backward_demodulation,[],[f62,f286])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f473,plain,(
% 0.21/0.54    spl6_37),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f472])).
% 0.21/0.54  fof(f472,plain,(
% 0.21/0.54    $false | spl6_37),
% 0.21/0.54    inference(subsumption_resolution,[],[f68,f471])).
% 0.21/0.54  fof(f471,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | spl6_37),
% 0.21/0.54    inference(resolution,[],[f398,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.21/0.54  fof(f398,plain,(
% 0.21/0.54    ~v1_funct_1(k1_xboole_0) | spl6_37),
% 0.21/0.54    inference(avatar_component_clause,[],[f397])).
% 0.21/0.54  fof(f470,plain,(
% 0.21/0.54    ~spl6_10 | ~spl6_27 | spl6_42),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f469])).
% 0.21/0.54  fof(f469,plain,(
% 0.21/0.54    $false | (~spl6_10 | ~spl6_27 | spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f432,f460])).
% 0.21/0.54  fof(f460,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | spl6_42),
% 0.21/0.54    inference(avatar_component_clause,[],[f459])).
% 0.21/0.54  fof(f459,plain,(
% 0.21/0.54    spl6_42 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.54  fof(f432,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_10 | ~spl6_27)),
% 0.21/0.54    inference(backward_demodulation,[],[f370,f289])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_10),
% 0.21/0.54    inference(backward_demodulation,[],[f63,f161])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f461,plain,(
% 0.21/0.54    spl6_41 | ~spl6_42 | ~spl6_10 | ~spl6_27),
% 0.21/0.54    inference(avatar_split_clause,[],[f445,f288,f160,f459,f456])).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_10 | ~spl6_27)),
% 0.21/0.54    inference(resolution,[],[f433,f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f61])).
% 0.21/0.54  fof(f433,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_10 | ~spl6_27)),
% 0.21/0.54    inference(backward_demodulation,[],[f371,f289])).
% 0.21/0.54  fof(f411,plain,(
% 0.21/0.54    ~spl6_26 | spl6_35),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.54  fof(f410,plain,(
% 0.21/0.54    $false | (~spl6_26 | spl6_35)),
% 0.21/0.54    inference(subsumption_resolution,[],[f383,f389])).
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    ~v1_relat_1(k1_xboole_0) | spl6_35),
% 0.21/0.54    inference(avatar_component_clause,[],[f388])).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0) | ~spl6_26),
% 0.21/0.54    inference(backward_demodulation,[],[f152,f286])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f64,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    ~spl6_10 | spl6_28),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f378])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    $false | (~spl6_10 | spl6_28)),
% 0.21/0.54    inference(subsumption_resolution,[],[f292,f370])).
% 0.21/0.54  fof(f292,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,sK0,k1_xboole_0) | spl6_28),
% 0.21/0.54    inference(avatar_component_clause,[],[f291])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    ~spl6_5 | ~spl6_1 | spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f367,f157,f139,f134,f119,f113,f127])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    spl6_9 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.54  fof(f367,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_6 | ~spl6_7 | ~spl6_9)),
% 0.21/0.54    inference(forward_demodulation,[],[f359,f228])).
% 0.21/0.54  fof(f359,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_7 | ~spl6_9)),
% 0.21/0.54    inference(superposition,[],[f74,f350])).
% 0.21/0.54  fof(f350,plain,(
% 0.21/0.54    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl6_7 | ~spl6_9)),
% 0.21/0.54    inference(backward_demodulation,[],[f140,f348])).
% 0.21/0.54  fof(f348,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK2) | ~spl6_9),
% 0.21/0.54    inference(forward_demodulation,[],[f151,f158])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f157])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    ~spl6_5 | ~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f364,f157,f139,f134,f116,f113,f127])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_6 | ~spl6_7 | ~spl6_9)),
% 0.21/0.54    inference(forward_demodulation,[],[f358,f228])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_7 | ~spl6_9)),
% 0.21/0.54    inference(superposition,[],[f73,f350])).
% 0.21/0.54  fof(f323,plain,(
% 0.21/0.54    spl6_9 | spl6_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f322,f160,f157])).
% 0.21/0.54  fof(f322,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(global_subsumption,[],[f63,f315])).
% 0.21/0.54  fof(f315,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f64,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f61])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    spl6_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    $false | spl6_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f62,f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | spl6_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    spl6_8 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    spl6_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    $false | spl6_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f152])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | spl6_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl6_4 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ~spl6_4 | ~spl6_8 | spl6_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f142,f113,f145,f124])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl6_1),
% 0.21/0.54    inference(resolution,[],[f114,f76])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl6_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f113])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ~spl6_4 | spl6_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f137,f139,f124])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(global_subsumption,[],[f62,f131])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f65,f78])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ~spl6_4 | spl6_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f132,f134,f124])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(global_subsumption,[],[f62,f130])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f65,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ~spl6_4 | spl6_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f122,f127,f124])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f62,f75])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f67,f119,f116,f113])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (1981)------------------------------
% 0.21/0.54  % (1981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1981)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (1981)Memory used [KB]: 11129
% 0.21/0.54  % (1981)Time elapsed: 0.135 s
% 0.21/0.54  % (1981)------------------------------
% 0.21/0.54  % (1981)------------------------------
% 0.21/0.54  % (2005)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (1987)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (1992)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (2009)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (1988)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (1991)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (2003)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (2001)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (2004)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (1998)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (2007)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (1997)Refutation not found, incomplete strategy% (1997)------------------------------
% 0.21/0.56  % (1997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1997)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1997)Memory used [KB]: 10618
% 0.21/0.56  % (1997)Time elapsed: 0.152 s
% 0.21/0.56  % (1997)------------------------------
% 0.21/0.56  % (1997)------------------------------
% 0.21/0.56  % (1995)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (1977)Success in time 0.195 s
%------------------------------------------------------------------------------
