%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:13 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  218 (1515 expanded)
%              Number of leaves         :   28 ( 375 expanded)
%              Depth                    :   25
%              Number of atoms          :  637 (8635 expanded)
%              Number of equality atoms :  136 (2066 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1065,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f124,f225,f314,f339,f363,f418,f541,f625,f700,f706,f1010])).

fof(f1010,plain,
    ( spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f1009])).

fof(f1009,plain,
    ( $false
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f1008,f988])).

fof(f988,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(backward_demodulation,[],[f981,f986])).

fof(f986,plain,
    ( ! [X12] : k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f985,f668])).

fof(f668,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f667,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f667,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | ~ r1_tarski(k1_xboole_0,k7_relat_1(k1_xboole_0,X0)) )
    | ~ spl6_21 ),
    inference(resolution,[],[f639,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
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

fof(f639,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl6_21 ),
    inference(resolution,[],[f627,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f627,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_21 ),
    inference(resolution,[],[f443,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f443,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl6_21
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f985,plain,
    ( ! [X12] : k7_relat_1(k1_xboole_0,X12) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f950,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f950,plain,
    ( ! [X12] : k7_relat_1(k1_xboole_0,X12) = k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,X12)
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f949,f668])).

fof(f949,plain,
    ( ! [X12,X11] : k7_relat_1(k7_relat_1(k1_xboole_0,X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k1_xboole_0,X11),X12)
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f948,f668])).

fof(f948,plain,
    ( ! [X12,X10,X11] : k7_relat_1(k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11),X12)
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f742,f747])).

fof(f747,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f733,f95])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f733,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f191,f123])).

fof(f123,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f191,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_11
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f742,plain,
    ( ! [X12,X10,X11] : k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f547,f123])).

fof(f547,plain,(
    ! [X12,X10,X11] : k2_partfun1(sK0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12) ),
    inference(subsumption_resolution,[],[f269,f279])).

fof(f279,plain,(
    ! [X0,X1] : v1_funct_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) ),
    inference(subsumption_resolution,[],[f278,f223])).

fof(f223,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f222,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f40])).

fof(f40,plain,
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f222,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f221,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f221,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f90,f146])).

fof(f146,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f140,f53])).

fof(f140,plain,(
    ! [X0] :
      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f278,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(k7_relat_1(sK3,X0),X1))
      | ~ v1_funct_1(k7_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f277,f151])).

fof(f151,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f150,f146])).

fof(f150,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f141,f53])).

fof(f141,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f277,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(k7_relat_1(sK3,X0),X1))
      | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(k7_relat_1(sK3,X0)) ) ),
    inference(superposition,[],[f90,f261])).

fof(f261,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK3,X0),X1) = k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) ),
    inference(resolution,[],[f212,f223])).

fof(f212,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_1(k7_relat_1(sK3,X5))
      | k2_partfun1(sK0,sK1,k7_relat_1(sK3,X5),X6) = k7_relat_1(k7_relat_1(sK3,X5),X6) ) ),
    inference(resolution,[],[f151,f89])).

fof(f269,plain,(
    ! [X12,X10,X11] :
      ( k2_partfun1(sK0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12)
      | ~ v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11)) ) ),
    inference(resolution,[],[f262,f89])).

fof(f262,plain,(
    ! [X0,X1] : m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f259,f261])).

fof(f259,plain,(
    ! [X0,X1] : m1_subset_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f213,f223])).

fof(f213,plain,(
    ! [X8,X7] :
      ( ~ v1_funct_1(k7_relat_1(sK3,X7))
      | m1_subset_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X7),X8),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(resolution,[],[f151,f91])).

fof(f981,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f980,f123])).

fof(f980,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f979,f747])).

fof(f979,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f978,f731])).

fof(f731,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(backward_demodulation,[],[f133,f123])).

fof(f133,plain,
    ( sK0 = sK2
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f978,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0)
    | spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f110,f118])).

fof(f110,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1008,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f798,f118])).

fof(f798,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f730,f747])).

fof(f730,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f54,f123])).

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f706,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f553,f131,f127])).

fof(f127,plain,
    ( spl6_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f553,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f56,f69])).

fof(f56,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f700,plain,
    ( spl6_3
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | spl6_3
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f693,f149])).

fof(f149,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(backward_demodulation,[],[f114,f146])).

fof(f114,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f693,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_16 ),
    inference(superposition,[],[f545,f610])).

fof(f610,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl6_16 ),
    inference(resolution,[],[f569,f56])).

fof(f569,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f568,f135])).

fof(f135,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f78])).

fof(f568,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl6_16 ),
    inference(superposition,[],[f61,f549])).

fof(f549,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f136,f338])).

fof(f338,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl6_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f136,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f55,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f545,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) ),
    inference(subsumption_resolution,[],[f206,f223])).

fof(f206,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))
      | ~ v1_funct_1(k7_relat_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f202,f159])).

fof(f159,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f158,f101])).

fof(f101,plain,(
    ! [X2,X0] :
      ( sP5(X2)
      | v1_relat_1(k7_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f101_D])).

fof(f101_D,plain,(
    ! [X2] :
      ( ! [X0] : v1_relat_1(k7_relat_1(X2,X0))
    <=> ~ sP5(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f158,plain,(
    ~ sP5(sK3) ),
    inference(subsumption_resolution,[],[f155,f135])).

fof(f155,plain,
    ( ~ v1_relat_1(sK3)
    | ~ sP5(sK3) ),
    inference(resolution,[],[f137,f102])).

fof(f102,plain,(
    ! [X2,X1] :
      ( ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ sP5(X2) ) ),
    inference(general_splitting,[],[f87,f101_D])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

fof(f137,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f55,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f202,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))
      | ~ v1_funct_1(k7_relat_1(sK3,X1))
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f198,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f198,plain,(
    ! [X2] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),sK1) ),
    inference(subsumption_resolution,[],[f195,f159])).

fof(f195,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X2)) ) ),
    inference(resolution,[],[f156,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f156,plain,(
    ! [X0] : v5_relat_1(k7_relat_1(sK3,X0),sK1) ),
    inference(subsumption_resolution,[],[f153,f135])).

fof(f153,plain,(
    ! [X0] :
      ( v5_relat_1(k7_relat_1(sK3,X0),sK1)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f137,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X2,X1)
      | v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f625,plain,(
    spl6_21 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | spl6_21 ),
    inference(subsumption_resolution,[],[f623,f59])).

fof(f623,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1))
    | spl6_21 ),
    inference(resolution,[],[f442,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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

fof(f442,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1)))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f441])).

fof(f541,plain,
    ( spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f539,f410])).

fof(f410,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f365,f374])).

fof(f374,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(sK3,X0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f373,f59])).

fof(f373,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k7_relat_1(sK3,X0))
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f372,f95])).

fof(f372,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),k7_relat_1(sK3,X0))
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f371,f123])).

fof(f371,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK3,X0)
        | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0)) )
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f353,f95])).

fof(f353,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = k2_zfmisc_1(k1_xboole_0,sK1)
        | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0)) )
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f220,f123])).

fof(f220,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0))
      | k2_zfmisc_1(sK0,sK1) = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f214,f69])).

fof(f214,plain,(
    ! [X9] : r1_tarski(k7_relat_1(sK3,X9),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f151,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f365,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f348,f95])).

fof(f348,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f151,f123])).

fof(f539,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f532,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f532,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f413,f118])).

fof(f413,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f149,f374])).

fof(f418,plain,
    ( ~ spl6_5
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f416,f364])).

fof(f364,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f346,f95])).

fof(f346,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f142,f123])).

fof(f142,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f73])).

fof(f416,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_5
    | spl6_11 ),
    inference(forward_demodulation,[],[f415,f374])).

fof(f415,plain,
    ( ! [X0] : ~ r1_tarski(sK3,k7_relat_1(sK3,X0))
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f379,f369])).

fof(f369,plain,
    ( k1_xboole_0 != sK3
    | ~ spl6_5
    | spl6_11 ),
    inference(forward_demodulation,[],[f350,f95])).

fof(f350,plain,
    ( sK3 != k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl6_5
    | spl6_11 ),
    inference(backward_demodulation,[],[f190,f123])).

fof(f190,plain,
    ( sK3 != k2_zfmisc_1(sK0,sK1)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f189])).

fof(f379,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK3
        | ~ r1_tarski(sK3,k7_relat_1(sK3,X0)) )
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f193,f374])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,k7_relat_1(sK3,X0))
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f152,f69])).

fof(f152,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(resolution,[],[f135,f60])).

fof(f363,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | ~ spl6_5
    | spl6_6 ),
    inference(subsumption_resolution,[],[f343,f59])).

fof(f343,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_5
    | spl6_6 ),
    inference(backward_demodulation,[],[f129,f123])).

fof(f129,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f339,plain,
    ( spl6_16
    | spl6_4 ),
    inference(avatar_split_clause,[],[f143,f117,f336])).

fof(f143,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f138,f54])).

fof(f138,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f55,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f314,plain,
    ( spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f310,f148])).

fof(f148,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl6_2 ),
    inference(backward_demodulation,[],[f110,f146])).

fof(f310,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl6_4 ),
    inference(superposition,[],[f309,f233])).

fof(f233,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | spl6_4 ),
    inference(resolution,[],[f161,f56])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f160,f135])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | spl6_4 ),
    inference(superposition,[],[f61,f145])).

fof(f145,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl6_4 ),
    inference(backward_demodulation,[],[f136,f144])).

fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f143,f119])).

fof(f119,plain,
    ( k1_xboole_0 != sK1
    | spl6_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f309,plain,(
    ! [X0] : v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(resolution,[],[f205,f223])).

fof(f205,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k7_relat_1(sK3,X0))
      | v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) ) ),
    inference(subsumption_resolution,[],[f201,f159])).

fof(f201,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f198,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f225,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f223,f147])).

fof(f147,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl6_1 ),
    inference(backward_demodulation,[],[f106,f146])).

fof(f106,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f124,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f57,f121,f117])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f115,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f58,f112,f108,f104])).

fof(f58,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:27:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (32404)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (32396)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (32388)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (32390)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (32408)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (32383)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (32385)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (32409)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32411)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (32404)Refutation not found, incomplete strategy% (32404)------------------------------
% 0.21/0.54  % (32404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32404)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  % (32382)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  
% 0.21/0.54  % (32404)Memory used [KB]: 10874
% 0.21/0.54  % (32404)Time elapsed: 0.080 s
% 0.21/0.54  % (32404)------------------------------
% 0.21/0.54  % (32404)------------------------------
% 0.21/0.54  % (32384)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (32387)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (32389)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (32381)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (32412)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (32399)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (32401)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (32402)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (32400)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (32391)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (32406)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (32397)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (32394)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (32392)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (32398)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (32395)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (32386)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (32405)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (32407)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.60  % (32403)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.83/0.60  % (32389)Refutation found. Thanks to Tanya!
% 1.83/0.60  % SZS status Theorem for theBenchmark
% 1.83/0.60  % SZS output start Proof for theBenchmark
% 1.83/0.60  fof(f1065,plain,(
% 1.83/0.60    $false),
% 1.83/0.60    inference(avatar_sat_refutation,[],[f115,f124,f225,f314,f339,f363,f418,f541,f625,f700,f706,f1010])).
% 1.83/0.60  fof(f1010,plain,(
% 1.83/0.60    spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | ~spl6_21),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f1009])).
% 1.83/0.60  fof(f1009,plain,(
% 1.83/0.60    $false | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | ~spl6_21)),
% 1.83/0.60    inference(subsumption_resolution,[],[f1008,f988])).
% 1.83/0.60  fof(f988,plain,(
% 1.83/0.60    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | ~spl6_21)),
% 1.83/0.60    inference(backward_demodulation,[],[f981,f986])).
% 1.83/0.60  fof(f986,plain,(
% 1.83/0.60    ( ! [X12] : (k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)) ) | (~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_21)),
% 1.83/0.60    inference(forward_demodulation,[],[f985,f668])).
% 1.83/0.60  fof(f668,plain,(
% 1.83/0.60    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl6_21),
% 1.83/0.60    inference(subsumption_resolution,[],[f667,f59])).
% 1.83/0.60  fof(f59,plain,(
% 1.83/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f3])).
% 1.83/0.60  fof(f3,axiom,(
% 1.83/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.83/0.60  fof(f667,plain,(
% 1.83/0.60    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,k7_relat_1(k1_xboole_0,X0))) ) | ~spl6_21),
% 1.83/0.60    inference(resolution,[],[f639,f69])).
% 1.83/0.60  fof(f69,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f44])).
% 1.83/0.60  fof(f44,plain,(
% 1.83/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.60    inference(flattening,[],[f43])).
% 1.83/0.60  fof(f43,plain,(
% 1.83/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.60    inference(nnf_transformation,[],[f2])).
% 1.83/0.60  fof(f2,axiom,(
% 1.83/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.83/0.60  fof(f639,plain,(
% 1.83/0.60    ( ! [X0] : (r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl6_21),
% 1.83/0.60    inference(resolution,[],[f627,f60])).
% 1.83/0.60  fof(f60,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f22])).
% 1.83/0.60  fof(f22,plain,(
% 1.83/0.60    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.83/0.60    inference(ennf_transformation,[],[f7])).
% 1.83/0.60  fof(f7,axiom,(
% 1.83/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.83/0.60  fof(f627,plain,(
% 1.83/0.60    v1_relat_1(k1_xboole_0) | ~spl6_21),
% 1.83/0.60    inference(resolution,[],[f443,f78])).
% 1.83/0.60  fof(f78,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f29])).
% 1.83/0.60  fof(f29,plain,(
% 1.83/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.60    inference(ennf_transformation,[],[f10])).
% 1.83/0.60  fof(f10,axiom,(
% 1.83/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.83/0.60  fof(f443,plain,(
% 1.83/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1))) | ~spl6_21),
% 1.83/0.60    inference(avatar_component_clause,[],[f441])).
% 1.83/0.60  fof(f441,plain,(
% 1.83/0.60    spl6_21 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1)))),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.83/0.60  fof(f985,plain,(
% 1.83/0.60    ( ! [X12] : (k7_relat_1(k1_xboole_0,X12) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)) ) | (~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_21)),
% 1.83/0.60    inference(forward_demodulation,[],[f950,f118])).
% 1.83/0.60  fof(f118,plain,(
% 1.83/0.60    k1_xboole_0 = sK1 | ~spl6_4),
% 1.83/0.60    inference(avatar_component_clause,[],[f117])).
% 1.83/0.60  fof(f117,plain,(
% 1.83/0.60    spl6_4 <=> k1_xboole_0 = sK1),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.83/0.60  fof(f950,plain,(
% 1.83/0.60    ( ! [X12] : (k7_relat_1(k1_xboole_0,X12) = k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,X12)) ) | (~spl6_5 | ~spl6_11 | ~spl6_21)),
% 1.83/0.60    inference(forward_demodulation,[],[f949,f668])).
% 1.83/0.60  fof(f949,plain,(
% 1.83/0.60    ( ! [X12,X11] : (k7_relat_1(k7_relat_1(k1_xboole_0,X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k1_xboole_0,X11),X12)) ) | (~spl6_5 | ~spl6_11 | ~spl6_21)),
% 1.83/0.60    inference(forward_demodulation,[],[f948,f668])).
% 1.83/0.60  fof(f948,plain,(
% 1.83/0.60    ( ! [X12,X10,X11] : (k7_relat_1(k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11),X12)) ) | (~spl6_5 | ~spl6_11)),
% 1.83/0.60    inference(forward_demodulation,[],[f742,f747])).
% 1.83/0.60  fof(f747,plain,(
% 1.83/0.60    k1_xboole_0 = sK3 | (~spl6_5 | ~spl6_11)),
% 1.83/0.60    inference(forward_demodulation,[],[f733,f95])).
% 1.83/0.60  fof(f95,plain,(
% 1.83/0.60    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.83/0.60    inference(equality_resolution,[],[f76])).
% 1.83/0.60  fof(f76,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.83/0.60    inference(cnf_transformation,[],[f51])).
% 1.83/0.60  fof(f51,plain,(
% 1.83/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.83/0.60    inference(flattening,[],[f50])).
% 1.83/0.60  fof(f50,plain,(
% 1.83/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.83/0.60    inference(nnf_transformation,[],[f4])).
% 1.83/0.60  fof(f4,axiom,(
% 1.83/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.83/0.60  fof(f733,plain,(
% 1.83/0.60    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) | (~spl6_5 | ~spl6_11)),
% 1.83/0.60    inference(backward_demodulation,[],[f191,f123])).
% 1.83/0.60  fof(f123,plain,(
% 1.83/0.60    k1_xboole_0 = sK0 | ~spl6_5),
% 1.83/0.60    inference(avatar_component_clause,[],[f121])).
% 1.83/0.60  fof(f121,plain,(
% 1.83/0.60    spl6_5 <=> k1_xboole_0 = sK0),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.83/0.60  fof(f191,plain,(
% 1.83/0.60    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl6_11),
% 1.83/0.60    inference(avatar_component_clause,[],[f189])).
% 1.83/0.60  fof(f189,plain,(
% 1.83/0.60    spl6_11 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.83/0.60  fof(f742,plain,(
% 1.83/0.60    ( ! [X12,X10,X11] : (k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12)) ) | ~spl6_5),
% 1.83/0.60    inference(backward_demodulation,[],[f547,f123])).
% 1.83/0.60  fof(f547,plain,(
% 1.83/0.60    ( ! [X12,X10,X11] : (k2_partfun1(sK0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f269,f279])).
% 1.83/0.60  fof(f279,plain,(
% 1.83/0.60    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(k7_relat_1(sK3,X0),X1))) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f278,f223])).
% 1.83/0.60  fof(f223,plain,(
% 1.83/0.60    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f222,f53])).
% 1.83/0.60  fof(f53,plain,(
% 1.83/0.60    v1_funct_1(sK3)),
% 1.83/0.60    inference(cnf_transformation,[],[f41])).
% 1.83/0.60  fof(f41,plain,(
% 1.83/0.60    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.83/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f40])).
% 1.83/0.60  fof(f40,plain,(
% 1.83/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.83/0.60    introduced(choice_axiom,[])).
% 1.83/0.60  fof(f21,plain,(
% 1.83/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.83/0.60    inference(flattening,[],[f20])).
% 1.83/0.60  fof(f20,plain,(
% 1.83/0.60    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.83/0.60    inference(ennf_transformation,[],[f18])).
% 1.83/0.60  fof(f18,negated_conjecture,(
% 1.83/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.83/0.60    inference(negated_conjecture,[],[f17])).
% 1.83/0.60  fof(f17,conjecture,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.83/0.60  fof(f222,plain,(
% 1.83/0.60    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f221,f55])).
% 1.83/0.60  fof(f55,plain,(
% 1.83/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.83/0.60    inference(cnf_transformation,[],[f41])).
% 1.83/0.60  fof(f221,plain,(
% 1.83/0.60    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.83/0.60    inference(superposition,[],[f90,f146])).
% 1.83/0.60  fof(f146,plain,(
% 1.83/0.60    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f140,f53])).
% 1.83/0.60  fof(f140,plain,(
% 1.83/0.60    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) | ~v1_funct_1(sK3)) )),
% 1.83/0.60    inference(resolution,[],[f55,f89])).
% 1.83/0.60  fof(f89,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f37])).
% 1.83/0.60  fof(f37,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.83/0.60    inference(flattening,[],[f36])).
% 1.83/0.60  fof(f36,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.83/0.60    inference(ennf_transformation,[],[f15])).
% 1.83/0.60  fof(f15,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.83/0.60  fof(f90,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f39])).
% 1.83/0.60  fof(f39,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.83/0.60    inference(flattening,[],[f38])).
% 1.83/0.60  fof(f38,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.83/0.60    inference(ennf_transformation,[],[f14])).
% 1.83/0.60  fof(f14,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.83/0.60  fof(f278,plain,(
% 1.83/0.60    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) | ~v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f277,f151])).
% 1.83/0.60  fof(f151,plain,(
% 1.83/0.60    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.83/0.60    inference(forward_demodulation,[],[f150,f146])).
% 1.83/0.60  fof(f150,plain,(
% 1.83/0.60    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f141,f53])).
% 1.83/0.60  fof(f141,plain,(
% 1.83/0.60    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.83/0.60    inference(resolution,[],[f55,f91])).
% 1.83/0.60  fof(f91,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f39])).
% 1.83/0.60  fof(f277,plain,(
% 1.83/0.60    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.83/0.60    inference(superposition,[],[f90,f261])).
% 1.83/0.60  fof(f261,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK3,X0),X1) = k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1)) )),
% 1.83/0.60    inference(resolution,[],[f212,f223])).
% 1.83/0.60  fof(f212,plain,(
% 1.83/0.60    ( ! [X6,X5] : (~v1_funct_1(k7_relat_1(sK3,X5)) | k2_partfun1(sK0,sK1,k7_relat_1(sK3,X5),X6) = k7_relat_1(k7_relat_1(sK3,X5),X6)) )),
% 1.83/0.60    inference(resolution,[],[f151,f89])).
% 1.83/0.60  fof(f269,plain,(
% 1.83/0.60    ( ! [X12,X10,X11] : (k2_partfun1(sK0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12) | ~v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11))) )),
% 1.83/0.60    inference(resolution,[],[f262,f89])).
% 1.83/0.60  fof(f262,plain,(
% 1.83/0.60    ( ! [X0,X1] : (m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.83/0.60    inference(backward_demodulation,[],[f259,f261])).
% 1.83/0.60  fof(f259,plain,(
% 1.83/0.60    ( ! [X0,X1] : (m1_subset_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.83/0.60    inference(resolution,[],[f213,f223])).
% 1.83/0.60  fof(f213,plain,(
% 1.83/0.60    ( ! [X8,X7] : (~v1_funct_1(k7_relat_1(sK3,X7)) | m1_subset_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X7),X8),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.83/0.60    inference(resolution,[],[f151,f91])).
% 1.83/0.60  fof(f981,plain,(
% 1.83/0.60    ~v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11)),
% 1.83/0.60    inference(forward_demodulation,[],[f980,f123])).
% 1.83/0.60  fof(f980,plain,(
% 1.83/0.60    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11)),
% 1.83/0.60    inference(forward_demodulation,[],[f979,f747])).
% 1.83/0.60  fof(f979,plain,(
% 1.83/0.60    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7)),
% 1.83/0.60    inference(forward_demodulation,[],[f978,f731])).
% 1.83/0.60  fof(f731,plain,(
% 1.83/0.60    k1_xboole_0 = sK2 | (~spl6_5 | ~spl6_7)),
% 1.83/0.60    inference(backward_demodulation,[],[f133,f123])).
% 1.83/0.60  fof(f133,plain,(
% 1.83/0.60    sK0 = sK2 | ~spl6_7),
% 1.83/0.60    inference(avatar_component_clause,[],[f131])).
% 1.83/0.60  fof(f131,plain,(
% 1.83/0.60    spl6_7 <=> sK0 = sK2),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.83/0.60  fof(f978,plain,(
% 1.83/0.60    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0) | (spl6_2 | ~spl6_4)),
% 1.83/0.60    inference(forward_demodulation,[],[f110,f118])).
% 1.83/0.60  fof(f110,plain,(
% 1.83/0.60    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl6_2),
% 1.83/0.60    inference(avatar_component_clause,[],[f108])).
% 1.83/0.60  fof(f108,plain,(
% 1.83/0.60    spl6_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.83/0.60  fof(f1008,plain,(
% 1.83/0.60    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_11)),
% 1.83/0.60    inference(forward_demodulation,[],[f798,f118])).
% 1.83/0.60  fof(f798,plain,(
% 1.83/0.60    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (~spl6_5 | ~spl6_11)),
% 1.83/0.60    inference(backward_demodulation,[],[f730,f747])).
% 1.83/0.60  fof(f730,plain,(
% 1.83/0.60    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl6_5),
% 1.83/0.60    inference(backward_demodulation,[],[f54,f123])).
% 1.83/0.60  fof(f54,plain,(
% 1.83/0.60    v1_funct_2(sK3,sK0,sK1)),
% 1.83/0.60    inference(cnf_transformation,[],[f41])).
% 1.83/0.60  fof(f706,plain,(
% 1.83/0.60    ~spl6_6 | spl6_7),
% 1.83/0.60    inference(avatar_split_clause,[],[f553,f131,f127])).
% 1.83/0.60  fof(f127,plain,(
% 1.83/0.60    spl6_6 <=> r1_tarski(sK0,sK2)),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.83/0.60  fof(f553,plain,(
% 1.83/0.60    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 1.83/0.60    inference(resolution,[],[f56,f69])).
% 1.83/0.60  fof(f56,plain,(
% 1.83/0.60    r1_tarski(sK2,sK0)),
% 1.83/0.60    inference(cnf_transformation,[],[f41])).
% 1.83/0.60  fof(f700,plain,(
% 1.83/0.60    spl6_3 | ~spl6_16),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f699])).
% 1.83/0.60  fof(f699,plain,(
% 1.83/0.60    $false | (spl6_3 | ~spl6_16)),
% 1.83/0.60    inference(subsumption_resolution,[],[f693,f149])).
% 1.83/0.60  fof(f149,plain,(
% 1.83/0.60    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 1.83/0.60    inference(backward_demodulation,[],[f114,f146])).
% 1.83/0.60  fof(f114,plain,(
% 1.83/0.60    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 1.83/0.60    inference(avatar_component_clause,[],[f112])).
% 1.83/0.60  fof(f112,plain,(
% 1.83/0.60    spl6_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.83/0.60  fof(f693,plain,(
% 1.83/0.60    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_16),
% 1.83/0.60    inference(superposition,[],[f545,f610])).
% 1.83/0.60  fof(f610,plain,(
% 1.83/0.60    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl6_16),
% 1.83/0.60    inference(resolution,[],[f569,f56])).
% 1.83/0.60  fof(f569,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl6_16),
% 1.83/0.60    inference(subsumption_resolution,[],[f568,f135])).
% 1.83/0.60  fof(f135,plain,(
% 1.83/0.60    v1_relat_1(sK3)),
% 1.83/0.60    inference(resolution,[],[f55,f78])).
% 1.83/0.60  fof(f568,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl6_16),
% 1.83/0.60    inference(superposition,[],[f61,f549])).
% 1.83/0.60  fof(f549,plain,(
% 1.83/0.60    sK0 = k1_relat_1(sK3) | ~spl6_16),
% 1.83/0.60    inference(backward_demodulation,[],[f136,f338])).
% 1.83/0.60  fof(f338,plain,(
% 1.83/0.60    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_16),
% 1.83/0.60    inference(avatar_component_clause,[],[f336])).
% 1.83/0.60  fof(f336,plain,(
% 1.83/0.60    spl6_16 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.83/0.60  fof(f136,plain,(
% 1.83/0.60    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.83/0.60    inference(resolution,[],[f55,f79])).
% 1.83/0.60  fof(f79,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f30])).
% 1.83/0.60  fof(f30,plain,(
% 1.83/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.60    inference(ennf_transformation,[],[f12])).
% 1.83/0.60  fof(f12,axiom,(
% 1.83/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.83/0.60  fof(f61,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f24])).
% 1.83/0.60  fof(f24,plain,(
% 1.83/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.83/0.60    inference(flattening,[],[f23])).
% 1.83/0.60  fof(f23,plain,(
% 1.83/0.60    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.83/0.60    inference(ennf_transformation,[],[f8])).
% 1.83/0.60  fof(f8,axiom,(
% 1.83/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.83/0.60  fof(f545,plain,(
% 1.83/0.60    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f206,f223])).
% 1.83/0.60  fof(f206,plain,(
% 1.83/0.60    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) | ~v1_funct_1(k7_relat_1(sK3,X1))) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f202,f159])).
% 1.83/0.60  fof(f159,plain,(
% 1.83/0.60    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.83/0.60    inference(resolution,[],[f158,f101])).
% 1.83/0.60  fof(f101,plain,(
% 1.83/0.60    ( ! [X2,X0] : (sP5(X2) | v1_relat_1(k7_relat_1(X2,X0))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f101_D])).
% 1.83/0.60  fof(f101_D,plain,(
% 1.83/0.60    ( ! [X2] : (( ! [X0] : v1_relat_1(k7_relat_1(X2,X0)) ) <=> ~sP5(X2)) )),
% 1.83/0.60    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.83/0.60  fof(f158,plain,(
% 1.83/0.60    ~sP5(sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f155,f135])).
% 1.83/0.60  fof(f155,plain,(
% 1.83/0.60    ~v1_relat_1(sK3) | ~sP5(sK3)),
% 1.83/0.60    inference(resolution,[],[f137,f102])).
% 1.83/0.60  fof(f102,plain,(
% 1.83/0.60    ( ! [X2,X1] : (~v5_relat_1(X2,X1) | ~v1_relat_1(X2) | ~sP5(X2)) )),
% 1.83/0.60    inference(general_splitting,[],[f87,f101_D])).
% 1.83/0.60  fof(f87,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f35])).
% 1.83/0.60  fof(f35,plain,(
% 1.83/0.60    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 1.83/0.60    inference(flattening,[],[f34])).
% 1.83/0.60  fof(f34,plain,(
% 1.83/0.60    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 1.83/0.60    inference(ennf_transformation,[],[f9])).
% 1.83/0.60  fof(f9,axiom,(
% 1.83/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).
% 1.83/0.60  fof(f137,plain,(
% 1.83/0.60    v5_relat_1(sK3,sK1)),
% 1.83/0.60    inference(resolution,[],[f55,f80])).
% 1.83/0.60  fof(f80,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f31])).
% 1.83/0.60  fof(f31,plain,(
% 1.83/0.60    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.60    inference(ennf_transformation,[],[f19])).
% 1.83/0.60  fof(f19,plain,(
% 1.83/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.83/0.60    inference(pure_predicate_removal,[],[f11])).
% 1.83/0.60  fof(f11,axiom,(
% 1.83/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.83/0.60  fof(f202,plain,(
% 1.83/0.60    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) | ~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 1.83/0.60    inference(resolution,[],[f198,f66])).
% 1.83/0.60  fof(f66,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f27])).
% 1.83/0.60  fof(f27,plain,(
% 1.83/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.83/0.60    inference(flattening,[],[f26])).
% 1.83/0.60  fof(f26,plain,(
% 1.83/0.60    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.83/0.60    inference(ennf_transformation,[],[f16])).
% 1.83/0.60  fof(f16,axiom,(
% 1.83/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.83/0.60  fof(f198,plain,(
% 1.83/0.60    ( ! [X2] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),sK1)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f195,f159])).
% 1.83/0.60  fof(f195,plain,(
% 1.83/0.60    ( ! [X2] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X2))) )),
% 1.83/0.60    inference(resolution,[],[f156,f62])).
% 1.83/0.60  fof(f62,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f42])).
% 1.83/0.60  fof(f42,plain,(
% 1.83/0.60    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.83/0.60    inference(nnf_transformation,[],[f25])).
% 1.83/0.60  fof(f25,plain,(
% 1.83/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.83/0.60    inference(ennf_transformation,[],[f6])).
% 1.83/0.60  fof(f6,axiom,(
% 1.83/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.83/0.60  fof(f156,plain,(
% 1.83/0.60    ( ! [X0] : (v5_relat_1(k7_relat_1(sK3,X0),sK1)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f153,f135])).
% 1.83/0.60  fof(f153,plain,(
% 1.83/0.60    ( ! [X0] : (v5_relat_1(k7_relat_1(sK3,X0),sK1) | ~v1_relat_1(sK3)) )),
% 1.83/0.60    inference(resolution,[],[f137,f88])).
% 1.83/0.60  fof(f88,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~v5_relat_1(X2,X1) | v5_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f35])).
% 1.83/0.60  fof(f625,plain,(
% 1.83/0.60    spl6_21),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f624])).
% 1.83/0.60  fof(f624,plain,(
% 1.83/0.60    $false | spl6_21),
% 1.83/0.60    inference(subsumption_resolution,[],[f623,f59])).
% 1.83/0.60  fof(f623,plain,(
% 1.83/0.60    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1)) | spl6_21),
% 1.83/0.60    inference(resolution,[],[f442,f74])).
% 1.83/0.60  fof(f74,plain,(
% 1.83/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f49])).
% 1.83/0.60  fof(f49,plain,(
% 1.83/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.83/0.60    inference(nnf_transformation,[],[f5])).
% 1.83/0.60  fof(f5,axiom,(
% 1.83/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.83/0.60  fof(f442,plain,(
% 1.83/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1))) | spl6_21),
% 1.83/0.60    inference(avatar_component_clause,[],[f441])).
% 1.83/0.60  fof(f541,plain,(
% 1.83/0.60    spl6_3 | ~spl6_4 | ~spl6_5),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f540])).
% 1.83/0.60  fof(f540,plain,(
% 1.83/0.60    $false | (spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f539,f410])).
% 1.83/0.60  fof(f410,plain,(
% 1.83/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl6_5),
% 1.83/0.60    inference(backward_demodulation,[],[f365,f374])).
% 1.83/0.60  fof(f374,plain,(
% 1.83/0.60    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl6_5),
% 1.83/0.60    inference(subsumption_resolution,[],[f373,f59])).
% 1.83/0.60  fof(f373,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(k1_xboole_0,k7_relat_1(sK3,X0)) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl6_5),
% 1.83/0.60    inference(forward_demodulation,[],[f372,f95])).
% 1.83/0.60  fof(f372,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),k7_relat_1(sK3,X0)) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl6_5),
% 1.83/0.60    inference(forward_demodulation,[],[f371,f123])).
% 1.83/0.60  fof(f371,plain,(
% 1.83/0.60    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0))) ) | ~spl6_5),
% 1.83/0.60    inference(forward_demodulation,[],[f353,f95])).
% 1.83/0.60  fof(f353,plain,(
% 1.83/0.60    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_zfmisc_1(k1_xboole_0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0))) ) | ~spl6_5),
% 1.83/0.60    inference(backward_demodulation,[],[f220,f123])).
% 1.83/0.60  fof(f220,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0)) | k2_zfmisc_1(sK0,sK1) = k7_relat_1(sK3,X0)) )),
% 1.83/0.60    inference(resolution,[],[f214,f69])).
% 1.83/0.60  fof(f214,plain,(
% 1.83/0.60    ( ! [X9] : (r1_tarski(k7_relat_1(sK3,X9),k2_zfmisc_1(sK0,sK1))) )),
% 1.83/0.60    inference(resolution,[],[f151,f73])).
% 1.83/0.60  fof(f73,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f49])).
% 1.83/0.60  fof(f365,plain,(
% 1.83/0.60    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_5),
% 1.83/0.60    inference(forward_demodulation,[],[f348,f95])).
% 1.83/0.60  fof(f348,plain,(
% 1.83/0.60    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))) ) | ~spl6_5),
% 1.83/0.60    inference(backward_demodulation,[],[f151,f123])).
% 1.83/0.60  fof(f539,plain,(
% 1.83/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.83/0.60    inference(forward_demodulation,[],[f532,f94])).
% 1.83/0.60  fof(f94,plain,(
% 1.83/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.83/0.60    inference(equality_resolution,[],[f77])).
% 1.83/0.60  fof(f77,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.83/0.60    inference(cnf_transformation,[],[f51])).
% 1.83/0.60  fof(f532,plain,(
% 1.83/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.83/0.60    inference(backward_demodulation,[],[f413,f118])).
% 1.83/0.60  fof(f413,plain,(
% 1.83/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl6_3 | ~spl6_5)),
% 1.83/0.60    inference(backward_demodulation,[],[f149,f374])).
% 1.83/0.60  fof(f418,plain,(
% 1.83/0.60    ~spl6_5 | spl6_11),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f417])).
% 1.83/0.60  fof(f417,plain,(
% 1.83/0.60    $false | (~spl6_5 | spl6_11)),
% 1.83/0.60    inference(subsumption_resolution,[],[f416,f364])).
% 1.83/0.60  fof(f364,plain,(
% 1.83/0.60    r1_tarski(sK3,k1_xboole_0) | ~spl6_5),
% 1.83/0.60    inference(forward_demodulation,[],[f346,f95])).
% 1.83/0.60  fof(f346,plain,(
% 1.83/0.60    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl6_5),
% 1.83/0.60    inference(backward_demodulation,[],[f142,f123])).
% 1.83/0.60  fof(f142,plain,(
% 1.83/0.60    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.83/0.60    inference(resolution,[],[f55,f73])).
% 1.83/0.60  fof(f416,plain,(
% 1.83/0.60    ~r1_tarski(sK3,k1_xboole_0) | (~spl6_5 | spl6_11)),
% 1.83/0.60    inference(forward_demodulation,[],[f415,f374])).
% 1.83/0.60  fof(f415,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(sK3,k7_relat_1(sK3,X0))) ) | (~spl6_5 | spl6_11)),
% 1.83/0.60    inference(subsumption_resolution,[],[f379,f369])).
% 1.83/0.60  fof(f369,plain,(
% 1.83/0.60    k1_xboole_0 != sK3 | (~spl6_5 | spl6_11)),
% 1.83/0.60    inference(forward_demodulation,[],[f350,f95])).
% 1.83/0.60  fof(f350,plain,(
% 1.83/0.60    sK3 != k2_zfmisc_1(k1_xboole_0,sK1) | (~spl6_5 | spl6_11)),
% 1.83/0.60    inference(backward_demodulation,[],[f190,f123])).
% 1.83/0.60  fof(f190,plain,(
% 1.83/0.60    sK3 != k2_zfmisc_1(sK0,sK1) | spl6_11),
% 1.83/0.60    inference(avatar_component_clause,[],[f189])).
% 1.83/0.60  fof(f379,plain,(
% 1.83/0.60    ( ! [X0] : (k1_xboole_0 = sK3 | ~r1_tarski(sK3,k7_relat_1(sK3,X0))) ) | ~spl6_5),
% 1.83/0.60    inference(backward_demodulation,[],[f193,f374])).
% 1.83/0.60  fof(f193,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(sK3,k7_relat_1(sK3,X0)) | sK3 = k7_relat_1(sK3,X0)) )),
% 1.83/0.60    inference(resolution,[],[f152,f69])).
% 1.83/0.60  fof(f152,plain,(
% 1.83/0.60    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 1.83/0.60    inference(resolution,[],[f135,f60])).
% 1.83/0.60  fof(f363,plain,(
% 1.83/0.60    ~spl6_5 | spl6_6),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f362])).
% 1.83/0.60  fof(f362,plain,(
% 1.83/0.60    $false | (~spl6_5 | spl6_6)),
% 1.83/0.60    inference(subsumption_resolution,[],[f343,f59])).
% 1.83/0.60  fof(f343,plain,(
% 1.83/0.60    ~r1_tarski(k1_xboole_0,sK2) | (~spl6_5 | spl6_6)),
% 1.83/0.60    inference(backward_demodulation,[],[f129,f123])).
% 1.83/0.60  fof(f129,plain,(
% 1.83/0.60    ~r1_tarski(sK0,sK2) | spl6_6),
% 1.83/0.60    inference(avatar_component_clause,[],[f127])).
% 1.83/0.60  fof(f339,plain,(
% 1.83/0.60    spl6_16 | spl6_4),
% 1.83/0.60    inference(avatar_split_clause,[],[f143,f117,f336])).
% 1.83/0.60  fof(f143,plain,(
% 1.83/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f138,f54])).
% 1.83/0.60  fof(f138,plain,(
% 1.83/0.60    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.83/0.60    inference(resolution,[],[f55,f81])).
% 1.83/0.60  fof(f81,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.83/0.60    inference(cnf_transformation,[],[f52])).
% 1.83/0.60  fof(f52,plain,(
% 1.83/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.60    inference(nnf_transformation,[],[f33])).
% 1.83/0.60  fof(f33,plain,(
% 1.83/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.60    inference(flattening,[],[f32])).
% 1.83/0.60  fof(f32,plain,(
% 1.83/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.60    inference(ennf_transformation,[],[f13])).
% 1.83/0.60  fof(f13,axiom,(
% 1.83/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.83/0.60  fof(f314,plain,(
% 1.83/0.60    spl6_2 | spl6_4),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f313])).
% 1.83/0.60  fof(f313,plain,(
% 1.83/0.60    $false | (spl6_2 | spl6_4)),
% 1.83/0.60    inference(subsumption_resolution,[],[f310,f148])).
% 1.83/0.60  fof(f148,plain,(
% 1.83/0.60    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl6_2),
% 1.83/0.60    inference(backward_demodulation,[],[f110,f146])).
% 1.83/0.60  fof(f310,plain,(
% 1.83/0.60    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl6_4),
% 1.83/0.60    inference(superposition,[],[f309,f233])).
% 1.83/0.60  fof(f233,plain,(
% 1.83/0.60    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | spl6_4),
% 1.83/0.60    inference(resolution,[],[f161,f56])).
% 1.83/0.60  fof(f161,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | spl6_4),
% 1.83/0.60    inference(subsumption_resolution,[],[f160,f135])).
% 1.83/0.60  fof(f160,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | spl6_4),
% 1.83/0.60    inference(superposition,[],[f61,f145])).
% 1.83/0.60  fof(f145,plain,(
% 1.83/0.60    sK0 = k1_relat_1(sK3) | spl6_4),
% 1.83/0.60    inference(backward_demodulation,[],[f136,f144])).
% 1.83/0.60  fof(f144,plain,(
% 1.83/0.60    sK0 = k1_relset_1(sK0,sK1,sK3) | spl6_4),
% 1.83/0.60    inference(subsumption_resolution,[],[f143,f119])).
% 1.83/0.60  fof(f119,plain,(
% 1.83/0.60    k1_xboole_0 != sK1 | spl6_4),
% 1.83/0.60    inference(avatar_component_clause,[],[f117])).
% 1.83/0.60  fof(f309,plain,(
% 1.83/0.60    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.83/0.60    inference(resolution,[],[f205,f223])).
% 1.83/0.60  fof(f205,plain,(
% 1.83/0.60    ( ! [X0] : (~v1_funct_1(k7_relat_1(sK3,X0)) | v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f201,f159])).
% 1.83/0.60  fof(f201,plain,(
% 1.83/0.60    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.83/0.60    inference(resolution,[],[f198,f65])).
% 1.83/0.60  fof(f65,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f27])).
% 1.83/0.60  fof(f225,plain,(
% 1.83/0.60    spl6_1),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f224])).
% 1.83/0.60  fof(f224,plain,(
% 1.83/0.60    $false | spl6_1),
% 1.83/0.60    inference(resolution,[],[f223,f147])).
% 1.83/0.60  fof(f147,plain,(
% 1.83/0.60    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl6_1),
% 1.83/0.60    inference(backward_demodulation,[],[f106,f146])).
% 1.83/0.60  fof(f106,plain,(
% 1.83/0.60    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl6_1),
% 1.83/0.60    inference(avatar_component_clause,[],[f104])).
% 1.83/0.60  fof(f104,plain,(
% 1.83/0.60    spl6_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.83/0.60  fof(f124,plain,(
% 1.83/0.60    ~spl6_4 | spl6_5),
% 1.83/0.60    inference(avatar_split_clause,[],[f57,f121,f117])).
% 1.83/0.60  fof(f57,plain,(
% 1.83/0.60    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.83/0.60    inference(cnf_transformation,[],[f41])).
% 1.83/0.60  fof(f115,plain,(
% 1.83/0.60    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.83/0.60    inference(avatar_split_clause,[],[f58,f112,f108,f104])).
% 1.83/0.60  fof(f58,plain,(
% 1.83/0.60    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.83/0.60    inference(cnf_transformation,[],[f41])).
% 1.83/0.60  % SZS output end Proof for theBenchmark
% 1.83/0.60  % (32389)------------------------------
% 1.83/0.60  % (32389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (32389)Termination reason: Refutation
% 1.83/0.60  
% 1.83/0.60  % (32389)Memory used [KB]: 11001
% 1.83/0.60  % (32389)Time elapsed: 0.170 s
% 1.83/0.60  % (32389)------------------------------
% 1.83/0.60  % (32389)------------------------------
% 1.83/0.60  % (32380)Success in time 0.241 s
%------------------------------------------------------------------------------
