%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 647 expanded)
%              Number of leaves         :   30 ( 172 expanded)
%              Depth                    :   16
%              Number of atoms          :  552 (3275 expanded)
%              Number of equality atoms :  141 ( 984 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f767,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f104,f118,f149,f178,f274,f316,f362,f396,f425,f429,f508,f524,f541,f689,f732,f749])).

fof(f749,plain,
    ( spl5_3
    | ~ spl5_10
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | spl5_3
    | ~ spl5_10
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f747,f125])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f747,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_3
    | ~ spl5_10
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f746,f702])).

fof(f702,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_10 ),
    inference(resolution,[],[f627,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f627,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_10 ),
    inference(resolution,[],[f144,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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

fof(f144,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_10
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f746,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl5_3
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f745,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f745,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl5_3
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f94,f730])).

fof(f730,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f726,f448])).

fof(f448,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl5_29
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f726,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_27 ),
    inference(superposition,[],[f152,f361])).

fof(f361,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl5_27
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f152,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f65,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f732,plain,
    ( spl5_5
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f731])).

fof(f731,plain,
    ( $false
    | spl5_5
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f730,f102])).

fof(f102,plain,
    ( k1_xboole_0 != sK0
    | spl5_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f689,plain,
    ( spl5_2
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | spl5_2
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f669,f271])).

fof(f271,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f270])).

fof(f270,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f215,f218])).

fof(f218,plain,(
    ! [X10,X11] : k1_xboole_0 = k1_relset_1(X10,X11,k1_xboole_0) ),
    inference(forward_demodulation,[],[f214,f48])).

fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f214,plain,(
    ! [X10,X11] : k1_relat_1(k1_xboole_0) = k1_relset_1(X10,X11,k1_xboole_0) ),
    inference(resolution,[],[f125,f65])).

fof(f215,plain,(
    ! [X12] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X12,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X12) ) ),
    inference(resolution,[],[f125,f115])).

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f81,f77])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f669,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(superposition,[],[f575,f608])).

fof(f608,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f607,f77])).

fof(f607,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f177,f103])).

fof(f103,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f177,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_13
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f575,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f90,f103])).

fof(f90,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f541,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_13
    | spl5_27 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_13
    | spl5_27 ),
    inference(subsumption_resolution,[],[f539,f103])).

fof(f539,plain,
    ( k1_xboole_0 != sK0
    | ~ spl5_4
    | ~ spl5_13
    | spl5_27 ),
    inference(forward_demodulation,[],[f538,f218])).

fof(f538,plain,
    ( sK0 != k1_relset_1(sK0,sK1,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_13
    | spl5_27 ),
    inference(forward_demodulation,[],[f360,f532])).

fof(f532,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f531,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f531,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f177,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f360,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f359])).

fof(f524,plain,
    ( ~ spl5_5
    | ~ spl5_27
    | spl5_29 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_27
    | spl5_29 ),
    inference(global_subsumption,[],[f426,f449])).

fof(f449,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | spl5_29 ),
    inference(avatar_component_clause,[],[f447])).

fof(f426,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f410,f398])).

fof(f398,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f361,f103])).

fof(f410,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_5 ),
    inference(superposition,[],[f152,f103])).

fof(f508,plain,
    ( ~ spl5_3
    | ~ spl5_20
    | spl5_29 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_20
    | spl5_29 ),
    inference(subsumption_resolution,[],[f477,f48])).

fof(f477,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_20
    | spl5_29 ),
    inference(superposition,[],[f449,f452])).

fof(f452,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(resolution,[],[f441,f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f441,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(resolution,[],[f433,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f433,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f432,f76])).

fof(f432,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f93,f301])).

fof(f301,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl5_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f93,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f429,plain,
    ( ~ spl5_5
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl5_5
    | spl5_12 ),
    inference(subsumption_resolution,[],[f427,f50])).

fof(f427,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_5
    | spl5_12 ),
    inference(forward_demodulation,[],[f412,f77])).

fof(f412,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | ~ spl5_5
    | spl5_12 ),
    inference(superposition,[],[f173,f103])).

fof(f173,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_12
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f425,plain,
    ( ~ spl5_5
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl5_5
    | spl5_11 ),
    inference(subsumption_resolution,[],[f423,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f423,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_5
    | spl5_11 ),
    inference(forward_demodulation,[],[f409,f77])).

fof(f409,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl5_5
    | spl5_11 ),
    inference(superposition,[],[f148,f103])).

fof(f148,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl5_11
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f396,plain,
    ( ~ spl5_4
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl5_4
    | spl5_12 ),
    inference(subsumption_resolution,[],[f394,f50])).

fof(f394,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_4
    | spl5_12 ),
    inference(forward_demodulation,[],[f380,f76])).

fof(f380,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | ~ spl5_4
    | spl5_12 ),
    inference(superposition,[],[f173,f98])).

fof(f362,plain,
    ( spl5_27
    | spl5_4 ),
    inference(avatar_split_clause,[],[f163,f97,f359])).

fof(f163,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f160,f42])).

fof(f42,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f160,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f67,f43])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f316,plain,
    ( spl5_2
    | spl5_4
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl5_2
    | spl5_4
    | spl5_20 ),
    inference(global_subsumption,[],[f297,f307,f300])).

fof(f300,plain,
    ( k1_xboole_0 != sK2
    | spl5_20 ),
    inference(avatar_component_clause,[],[f299])).

fof(f307,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl5_4 ),
    inference(forward_demodulation,[],[f293,f201])).

fof(f201,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl5_4 ),
    inference(superposition,[],[f152,f164])).

fof(f164,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f163,f99])).

fof(f99,plain,
    ( k1_xboole_0 != sK1
    | spl5_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f293,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | spl5_4 ),
    inference(resolution,[],[f272,f65])).

fof(f272,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_4 ),
    inference(resolution,[],[f265,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | spl5_4 ),
    inference(forward_demodulation,[],[f264,f201])).

fof(f264,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f261,f128])).

fof(f128,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f127,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f127,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f261,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f206,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f206,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(superposition,[],[f44,f155])).

fof(f155,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f66,f43])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f44,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f297,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f290,f90])).

fof(f290,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | spl5_4 ),
    inference(resolution,[],[f272,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f274,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f272,f94])).

fof(f178,plain,
    ( ~ spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f168,f175,f171])).

fof(f168,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    inference(resolution,[],[f123,f58])).

fof(f123,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f43])).

fof(f149,plain,
    ( spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f141,f146,f143])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f73,f43])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f118,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f86,f41])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f104,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f45,f101,f97])).

fof(f45,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f46,f92,f88,f84])).

fof(f46,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:04:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (15335)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (15343)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (15335)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f767,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f95,f104,f118,f149,f178,f274,f316,f362,f396,f425,f429,f508,f524,f541,f689,f732,f749])).
% 0.21/0.50  fof(f749,plain,(
% 0.21/0.50    spl5_3 | ~spl5_10 | ~spl5_27 | ~spl5_29),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f748])).
% 0.21/0.50  fof(f748,plain,(
% 0.21/0.50    $false | (spl5_3 | ~spl5_10 | ~spl5_27 | ~spl5_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f747,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f60,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f747,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl5_3 | ~spl5_10 | ~spl5_27 | ~spl5_29)),
% 0.21/0.50    inference(forward_demodulation,[],[f746,f702])).
% 0.21/0.50  fof(f702,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | ~spl5_10),
% 0.21/0.50    inference(resolution,[],[f627,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.50  fof(f627,plain,(
% 0.21/0.50    v1_xboole_0(sK3) | ~spl5_10),
% 0.21/0.50    inference(resolution,[],[f144,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(rectify,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl5_10 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f746,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (spl5_3 | ~spl5_27 | ~spl5_29)),
% 0.21/0.50    inference(forward_demodulation,[],[f745,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    inference(flattening,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f745,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl5_3 | ~spl5_27 | ~spl5_29)),
% 0.21/0.50    inference(forward_demodulation,[],[f94,f730])).
% 0.21/0.50  fof(f730,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | (~spl5_27 | ~spl5_29)),
% 0.21/0.50    inference(forward_demodulation,[],[f726,f448])).
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK3) | ~spl5_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f447])).
% 0.21/0.50  fof(f447,plain,(
% 0.21/0.50    spl5_29 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.50  fof(f726,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~spl5_27),
% 0.21/0.50    inference(superposition,[],[f152,f361])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f359])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    spl5_27 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f65,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f732,plain,(
% 0.21/0.50    spl5_5 | ~spl5_27 | ~spl5_29),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f731])).
% 0.21/0.50  fof(f731,plain,(
% 0.21/0.50    $false | (spl5_5 | ~spl5_27 | ~spl5_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f730,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    k1_xboole_0 != sK0 | spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl5_5 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f689,plain,(
% 0.21/0.50    spl5_2 | ~spl5_5 | ~spl5_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f688])).
% 0.21/0.50  fof(f688,plain,(
% 0.21/0.50    $false | (spl5_2 | ~spl5_5 | ~spl5_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f669,f271])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f270])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f215,f218])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ( ! [X10,X11] : (k1_xboole_0 = k1_relset_1(X10,X11,k1_xboole_0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f214,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ( ! [X10,X11] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X10,X11,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f125,f65])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    ( ! [X12] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X12,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X12)) )),
% 0.21/0.50    inference(resolution,[],[f125,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f81,f77])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f669,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (spl5_2 | ~spl5_5 | ~spl5_13)),
% 0.21/0.50    inference(superposition,[],[f575,f608])).
% 0.21/0.50  fof(f608,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | (~spl5_5 | ~spl5_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f607,f77])).
% 0.21/0.50  fof(f607,plain,(
% 0.21/0.50    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) | (~spl5_5 | ~spl5_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f177,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl5_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl5_13 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f575,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl5_2 | ~spl5_5)),
% 0.21/0.50    inference(superposition,[],[f90,f103])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,sK2) | spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl5_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f541,plain,(
% 0.21/0.50    ~spl5_4 | ~spl5_5 | ~spl5_13 | spl5_27),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f540])).
% 0.21/0.50  fof(f540,plain,(
% 0.21/0.50    $false | (~spl5_4 | ~spl5_5 | ~spl5_13 | spl5_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f539,f103])).
% 0.21/0.50  fof(f539,plain,(
% 0.21/0.50    k1_xboole_0 != sK0 | (~spl5_4 | ~spl5_13 | spl5_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f538,f218])).
% 0.21/0.50  fof(f538,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK1,k1_xboole_0) | (~spl5_4 | ~spl5_13 | spl5_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f360,f532])).
% 0.21/0.50  fof(f532,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | (~spl5_4 | ~spl5_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f531,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f531,plain,(
% 0.21/0.50    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl5_4 | ~spl5_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f177,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl5_4 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK1,sK3) | spl5_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f359])).
% 0.21/0.50  fof(f524,plain,(
% 0.21/0.50    ~spl5_5 | ~spl5_27 | spl5_29),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f523])).
% 0.21/0.50  fof(f523,plain,(
% 0.21/0.50    $false | (~spl5_5 | ~spl5_27 | spl5_29)),
% 0.21/0.50    inference(global_subsumption,[],[f426,f449])).
% 0.21/0.50  fof(f449,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(sK3) | spl5_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f447])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK3) | (~spl5_5 | ~spl5_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f410,f398])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl5_5 | ~spl5_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f361,f103])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl5_5),
% 0.21/0.50    inference(superposition,[],[f152,f103])).
% 0.21/0.50  fof(f508,plain,(
% 0.21/0.50    ~spl5_3 | ~spl5_20 | spl5_29),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f507])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    $false | (~spl5_3 | ~spl5_20 | spl5_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f477,f48])).
% 0.21/0.50  fof(f477,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl5_3 | ~spl5_20 | spl5_29)),
% 0.21/0.50    inference(superposition,[],[f449,f452])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | (~spl5_3 | ~spl5_20)),
% 0.21/0.50    inference(resolution,[],[f441,f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(resolution,[],[f58,f50])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f441,plain,(
% 0.21/0.51    r1_tarski(sK3,k1_xboole_0) | (~spl5_3 | ~spl5_20)),
% 0.21/0.51    inference(resolution,[],[f433,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl5_3 | ~spl5_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f432,f76])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl5_3 | ~spl5_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f93,f301])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl5_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f299])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    spl5_20 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    ~spl5_5 | spl5_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    $false | (~spl5_5 | spl5_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f427,f50])).
% 0.21/0.51  fof(f427,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,sK3) | (~spl5_5 | spl5_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f412,f77])).
% 0.21/0.51  fof(f412,plain,(
% 0.21/0.51    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | (~spl5_5 | spl5_12)),
% 0.21/0.51    inference(superposition,[],[f173,f103])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl5_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl5_12 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    ~spl5_5 | spl5_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f424])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    $false | (~spl5_5 | spl5_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f423,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | (~spl5_5 | spl5_11)),
% 0.21/0.51    inference(forward_demodulation,[],[f409,f77])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl5_5 | spl5_11)),
% 0.21/0.51    inference(superposition,[],[f148,f103])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl5_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    spl5_11 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    ~spl5_4 | spl5_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f395])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    $false | (~spl5_4 | spl5_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f394,f50])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,sK3) | (~spl5_4 | spl5_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f380,f76])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | (~spl5_4 | spl5_12)),
% 0.21/0.51    inference(superposition,[],[f173,f98])).
% 0.21/0.51  fof(f362,plain,(
% 0.21/0.51    spl5_27 | spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f163,f97,f359])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f160,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.51    inference(resolution,[],[f67,f43])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    spl5_2 | spl5_4 | spl5_20),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f315])).
% 0.21/0.51  fof(f315,plain,(
% 0.21/0.51    $false | (spl5_2 | spl5_4 | spl5_20)),
% 0.21/0.51    inference(global_subsumption,[],[f297,f307,f300])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | spl5_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f299])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK2,sK3) | spl5_4),
% 0.21/0.51    inference(forward_demodulation,[],[f293,f201])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | spl5_4),
% 0.21/0.51    inference(superposition,[],[f152,f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | spl5_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | spl5_4),
% 0.21/0.51    inference(resolution,[],[f272,f65])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_4),
% 0.21/0.51    inference(resolution,[],[f265,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | spl5_4),
% 0.21/0.51    inference(forward_demodulation,[],[f264,f201])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f261,f128])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    v1_relat_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f52,f43])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 0.21/0.51    inference(resolution,[],[f206,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.51    inference(superposition,[],[f44,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f66,f43])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | (spl5_2 | spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f290,f90])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | spl5_4),
% 0.21/0.51    inference(resolution,[],[f272,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    spl5_3 | spl5_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f273])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    $false | (spl5_3 | spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f272,f94])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~spl5_12 | spl5_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f168,f175,f171])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    sK3 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 0.21/0.52    inference(resolution,[],[f123,f58])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f59,f43])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl5_10 | ~spl5_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f141,f146,f143])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.52    inference(resolution,[],[f73,f43])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl5_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    $false | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f86,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~spl5_4 | spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f45,f101,f97])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f46,f92,f88,f84])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15335)------------------------------
% 0.21/0.52  % (15335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15335)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15335)Memory used [KB]: 11001
% 0.21/0.52  % (15335)Time elapsed: 0.068 s
% 0.21/0.52  % (15335)------------------------------
% 0.21/0.52  % (15335)------------------------------
% 0.21/0.52  % (15324)Success in time 0.159 s
%------------------------------------------------------------------------------
