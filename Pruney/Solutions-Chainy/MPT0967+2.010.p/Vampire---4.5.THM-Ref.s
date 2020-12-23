%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:43 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 742 expanded)
%              Number of leaves         :   28 ( 186 expanded)
%              Depth                    :   20
%              Number of atoms          :  521 (3616 expanded)
%              Number of equality atoms :  123 ( 888 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1574,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f115,f117,f129,f502,f610,f675,f838,f1483,f1573])).

fof(f1573,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f1572])).

fof(f1572,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | spl6_9 ),
    inference(subsumption_resolution,[],[f1568,f1535])).

fof(f1535,plain,
    ( k1_xboole_0 != sK3
    | ~ spl6_4
    | spl6_9 ),
    inference(forward_demodulation,[],[f1534,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1534,plain,
    ( sK3 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl6_4
    | spl6_9 ),
    inference(forward_demodulation,[],[f154,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f154,plain,
    ( sK3 != k2_zfmisc_1(sK0,sK1)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_9
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1568,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_5 ),
    inference(resolution,[],[f1349,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f1349,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f1348,f86])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1348,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK2))
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f618,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f618,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f608,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f608,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f234,f137])).

fof(f137,plain,(
    sP5(sK3,sK0) ),
    inference(resolution,[],[f51,f92])).

fof(f92,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | sP5(X3,X2) ) ),
    inference(cnf_transformation,[],[f92_D])).

fof(f92_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    <=> ~ sP5(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
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
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f234,plain,(
    ! [X0] :
      ( ~ sP5(sK3,X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(resolution,[],[f220,f93])).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ sP5(X3,X2) ) ),
    inference(general_splitting,[],[f82,f92_D])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f220,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f209,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f209,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f174,f143])).

fof(f143,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f142,f136])).

fof(f136,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f142,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f134,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f134,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(X1,sK2)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f118,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f118,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f52,f81])).

fof(f52,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f1483,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | spl6_32 ),
    inference(avatar_contradiction_clause,[],[f1482])).

fof(f1482,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | spl6_32 ),
    inference(subsumption_resolution,[],[f1480,f1437])).

fof(f1437,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | spl6_32 ),
    inference(backward_demodulation,[],[f1324,f1394])).

fof(f1394,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1393,f85])).

fof(f1393,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f155,f109])).

fof(f155,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f1324,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl6_5
    | spl6_32 ),
    inference(forward_demodulation,[],[f488,f114])).

fof(f488,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl6_32 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl6_32
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f1480,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f1438,f1474])).

fof(f1474,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f1473,f56])).

fof(f1473,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f1472,f66])).

fof(f1472,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1471,f1433])).

fof(f1433,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f1149,f1394])).

fof(f1149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f1148,f85])).

fof(f1148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f51,f109])).

fof(f1471,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1470,f85])).

fof(f1470,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(superposition,[],[f73,f1435])).

fof(f1435,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f1170,f1394])).

fof(f1170,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f1169,f114])).

fof(f1169,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f135,f109])).

fof(f135,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f51,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f1438,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f1327,f1394])).

fof(f1327,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f615,f114])).

fof(f615,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f608,f72])).

fof(f838,plain,
    ( spl6_2
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f837])).

fof(f837,plain,
    ( $false
    | spl6_2
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f753,f626])).

fof(f626,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl6_2
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f101,f624])).

fof(f624,plain,
    ( k1_xboole_0 = sK2
    | spl6_2
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f619,f101])).

fof(f619,plain,
    ( k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f613,f487])).

fof(f487,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f486])).

fof(f613,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f608,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f101,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f753,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl6_2
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f50,f747])).

fof(f747,plain,
    ( k1_xboole_0 = sK1
    | spl6_2
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f128,f624])).

fof(f128,plain,
    ( sK1 = sK2
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f675,plain,
    ( spl6_2
    | spl6_6
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | spl6_2
    | spl6_6
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f632,f55])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f632,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_2
    | spl6_6
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f131,f624])).

fof(f131,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_6 ),
    inference(resolution,[],[f130,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f130,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | spl6_6 ),
    inference(resolution,[],[f124,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f124,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f610,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f608,f105])).

fof(f105,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f502,plain,
    ( ~ spl6_3
    | spl6_4
    | spl6_32 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl6_3
    | spl6_4
    | spl6_32 ),
    inference(subsumption_resolution,[],[f500,f488])).

fof(f500,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_3
    | spl6_4 ),
    inference(forward_demodulation,[],[f496,f141])).

fof(f141,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl6_4 ),
    inference(forward_demodulation,[],[f135,f140])).

fof(f140,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f139,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK1
    | spl6_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f132,f50])).

fof(f132,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f496,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f104,f72])).

fof(f104,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f129,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f120,f126,f122])).

fof(f120,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f52,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f117,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f97,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f115,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f53,f112,f108])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f106,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f54,f103,f99,f95])).

fof(f54,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:39:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (6555)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (6547)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (6544)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (6534)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (6535)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (6533)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (6545)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (6550)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.53  % (6548)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.53  % (6539)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.53  % (6552)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.53  % (6537)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.54  % (6536)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.54  % (6560)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (6538)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  % (6546)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.54  % (6542)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.54  % (6543)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.55  % (6540)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.55  % (6559)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.55  % (6541)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.55  % (6561)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.55  % (6549)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.55  % (6551)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.55  % (6562)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.56  % (6553)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.56  % (6558)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.56  % (6556)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.56  % (6557)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.56  % (6554)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.61  % (6541)Refutation found. Thanks to Tanya!
% 1.49/0.61  % SZS status Theorem for theBenchmark
% 1.49/0.61  % SZS output start Proof for theBenchmark
% 1.49/0.61  fof(f1574,plain,(
% 1.49/0.61    $false),
% 1.49/0.61    inference(avatar_sat_refutation,[],[f106,f115,f117,f129,f502,f610,f675,f838,f1483,f1573])).
% 1.49/0.61  fof(f1573,plain,(
% 1.49/0.61    ~spl6_4 | ~spl6_5 | spl6_9),
% 1.49/0.61    inference(avatar_contradiction_clause,[],[f1572])).
% 1.49/0.61  fof(f1572,plain,(
% 1.49/0.61    $false | (~spl6_4 | ~spl6_5 | spl6_9)),
% 1.49/0.61    inference(subsumption_resolution,[],[f1568,f1535])).
% 1.49/0.61  fof(f1535,plain,(
% 1.49/0.61    k1_xboole_0 != sK3 | (~spl6_4 | spl6_9)),
% 1.49/0.61    inference(forward_demodulation,[],[f1534,f85])).
% 1.49/0.61  fof(f85,plain,(
% 1.49/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.49/0.61    inference(equality_resolution,[],[f70])).
% 1.49/0.61  fof(f70,plain,(
% 1.49/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.49/0.61    inference(cnf_transformation,[],[f47])).
% 1.49/0.61  fof(f47,plain,(
% 1.49/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.49/0.61    inference(flattening,[],[f46])).
% 1.49/0.61  fof(f46,plain,(
% 1.49/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.49/0.61    inference(nnf_transformation,[],[f7])).
% 1.49/0.61  fof(f7,axiom,(
% 1.49/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.49/0.61  fof(f1534,plain,(
% 1.49/0.61    sK3 != k2_zfmisc_1(sK0,k1_xboole_0) | (~spl6_4 | spl6_9)),
% 1.49/0.61    inference(forward_demodulation,[],[f154,f109])).
% 1.49/0.61  fof(f109,plain,(
% 1.49/0.61    k1_xboole_0 = sK1 | ~spl6_4),
% 1.49/0.61    inference(avatar_component_clause,[],[f108])).
% 1.49/0.61  fof(f108,plain,(
% 1.49/0.61    spl6_4 <=> k1_xboole_0 = sK1),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.49/0.61  fof(f154,plain,(
% 1.49/0.61    sK3 != k2_zfmisc_1(sK0,sK1) | spl6_9),
% 1.49/0.61    inference(avatar_component_clause,[],[f153])).
% 1.49/0.61  fof(f153,plain,(
% 1.49/0.61    spl6_9 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.49/0.61  fof(f1568,plain,(
% 1.49/0.61    k1_xboole_0 = sK3 | ~spl6_5),
% 1.49/0.61    inference(resolution,[],[f1349,f56])).
% 1.49/0.61  fof(f56,plain,(
% 1.49/0.61    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.49/0.61    inference(cnf_transformation,[],[f22])).
% 1.49/0.61  fof(f22,plain,(
% 1.49/0.61    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.49/0.61    inference(ennf_transformation,[],[f6])).
% 1.49/0.61  fof(f6,axiom,(
% 1.49/0.61    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.49/0.61  fof(f1349,plain,(
% 1.49/0.61    r1_tarski(sK3,k1_xboole_0) | ~spl6_5),
% 1.49/0.61    inference(forward_demodulation,[],[f1348,f86])).
% 1.49/0.61  fof(f86,plain,(
% 1.49/0.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.49/0.61    inference(equality_resolution,[],[f69])).
% 1.49/0.61  fof(f69,plain,(
% 1.49/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.49/0.61    inference(cnf_transformation,[],[f47])).
% 1.49/0.61  fof(f1348,plain,(
% 1.49/0.61    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK2)) | ~spl6_5),
% 1.49/0.61    inference(forward_demodulation,[],[f618,f114])).
% 1.49/0.61  fof(f114,plain,(
% 1.49/0.61    k1_xboole_0 = sK0 | ~spl6_5),
% 1.49/0.61    inference(avatar_component_clause,[],[f112])).
% 1.49/0.61  fof(f112,plain,(
% 1.49/0.61    spl6_5 <=> k1_xboole_0 = sK0),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.49/0.61  fof(f618,plain,(
% 1.49/0.61    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 1.49/0.61    inference(resolution,[],[f608,f66])).
% 1.49/0.61  fof(f66,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f45])).
% 1.49/0.61  fof(f45,plain,(
% 1.49/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.49/0.61    inference(nnf_transformation,[],[f8])).
% 1.49/0.61  fof(f8,axiom,(
% 1.49/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.61  fof(f608,plain,(
% 1.49/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.49/0.61    inference(resolution,[],[f234,f137])).
% 1.49/0.61  fof(f137,plain,(
% 1.49/0.61    sP5(sK3,sK0)),
% 1.49/0.61    inference(resolution,[],[f51,f92])).
% 1.49/0.61  fof(f92,plain,(
% 1.49/0.61    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | sP5(X3,X2)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f92_D])).
% 1.49/0.61  fof(f92_D,plain,(
% 1.49/0.61    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) <=> ~sP5(X3,X2)) )),
% 1.49/0.61    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.49/0.61  fof(f51,plain,(
% 1.49/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.61    inference(cnf_transformation,[],[f37])).
% 1.49/0.61  fof(f37,plain,(
% 1.49/0.61    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.49/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f36])).
% 1.49/0.61  fof(f36,plain,(
% 1.49/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.49/0.61    introduced(choice_axiom,[])).
% 1.49/0.61  fof(f21,plain,(
% 1.49/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.49/0.61    inference(flattening,[],[f20])).
% 1.49/0.61  fof(f20,plain,(
% 1.49/0.61    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.49/0.61    inference(ennf_transformation,[],[f17])).
% 1.49/0.61  fof(f17,negated_conjecture,(
% 1.49/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.49/0.61    inference(negated_conjecture,[],[f16])).
% 1.49/0.61  fof(f16,conjecture,(
% 1.49/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 1.49/0.61  fof(f234,plain,(
% 1.49/0.61    ( ! [X0] : (~sP5(sK3,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 1.49/0.61    inference(resolution,[],[f220,f93])).
% 1.49/0.61  fof(f93,plain,(
% 1.49/0.61    ( ! [X2,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~sP5(X3,X2)) )),
% 1.49/0.61    inference(general_splitting,[],[f82,f92_D])).
% 1.49/0.61  fof(f82,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f35])).
% 1.49/0.61  fof(f35,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.49/0.61    inference(flattening,[],[f34])).
% 1.49/0.61  fof(f34,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.49/0.61    inference(ennf_transformation,[],[f14])).
% 1.49/0.61  fof(f14,axiom,(
% 1.49/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 1.49/0.61  fof(f220,plain,(
% 1.49/0.61    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.49/0.61    inference(subsumption_resolution,[],[f209,f84])).
% 1.49/0.61  fof(f84,plain,(
% 1.49/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.61    inference(equality_resolution,[],[f60])).
% 1.49/0.61  fof(f60,plain,(
% 1.49/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.49/0.61    inference(cnf_transformation,[],[f40])).
% 1.49/0.61  fof(f40,plain,(
% 1.49/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.61    inference(flattening,[],[f39])).
% 1.49/0.61  fof(f39,plain,(
% 1.49/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.61    inference(nnf_transformation,[],[f4])).
% 1.49/0.61  fof(f4,axiom,(
% 1.49/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.61  fof(f209,plain,(
% 1.49/0.61    r1_tarski(k2_relat_1(sK3),sK2) | ~r1_tarski(sK1,sK1)),
% 1.49/0.61    inference(resolution,[],[f174,f143])).
% 1.49/0.61  fof(f143,plain,(
% 1.49/0.61    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.49/0.61    inference(subsumption_resolution,[],[f142,f136])).
% 1.49/0.61  fof(f136,plain,(
% 1.49/0.61    v1_relat_1(sK3)),
% 1.49/0.61    inference(resolution,[],[f51,f71])).
% 1.49/0.61  fof(f71,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f26])).
% 1.49/0.61  fof(f26,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.61    inference(ennf_transformation,[],[f10])).
% 1.49/0.61  fof(f10,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.49/0.61  fof(f142,plain,(
% 1.49/0.61    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.49/0.61    inference(resolution,[],[f134,f58])).
% 1.49/0.61  fof(f58,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f38])).
% 1.49/0.61  fof(f38,plain,(
% 1.49/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.49/0.61    inference(nnf_transformation,[],[f24])).
% 1.49/0.61  fof(f24,plain,(
% 1.49/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.61    inference(ennf_transformation,[],[f9])).
% 1.49/0.61  fof(f9,axiom,(
% 1.49/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.49/0.61  fof(f134,plain,(
% 1.49/0.61    v5_relat_1(sK3,sK1)),
% 1.49/0.61    inference(resolution,[],[f51,f74])).
% 1.49/0.61  fof(f74,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f29])).
% 1.49/0.61  fof(f29,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.61    inference(ennf_transformation,[],[f19])).
% 1.49/0.61  fof(f19,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.49/0.61    inference(pure_predicate_removal,[],[f11])).
% 1.49/0.61  fof(f11,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.49/0.61  fof(f174,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(X1,sK2) | ~r1_tarski(X0,sK1)) )),
% 1.49/0.61    inference(resolution,[],[f118,f81])).
% 1.49/0.61  fof(f81,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f33])).
% 1.49/0.61  fof(f33,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.49/0.61    inference(flattening,[],[f32])).
% 1.49/0.61  fof(f32,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.49/0.61    inference(ennf_transformation,[],[f5])).
% 1.49/0.61  fof(f5,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.49/0.61  fof(f118,plain,(
% 1.49/0.61    ( ! [X0] : (r1_tarski(X0,sK2) | ~r1_tarski(X0,sK1)) )),
% 1.49/0.61    inference(resolution,[],[f52,f81])).
% 1.49/0.61  fof(f52,plain,(
% 1.49/0.61    r1_tarski(sK1,sK2)),
% 1.49/0.61    inference(cnf_transformation,[],[f37])).
% 1.49/0.61  fof(f1483,plain,(
% 1.49/0.61    ~spl6_4 | ~spl6_5 | ~spl6_9 | spl6_32),
% 1.49/0.61    inference(avatar_contradiction_clause,[],[f1482])).
% 1.49/0.61  fof(f1482,plain,(
% 1.49/0.61    $false | (~spl6_4 | ~spl6_5 | ~spl6_9 | spl6_32)),
% 1.49/0.61    inference(subsumption_resolution,[],[f1480,f1437])).
% 1.49/0.61  fof(f1437,plain,(
% 1.49/0.61    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_9 | spl6_32)),
% 1.49/0.61    inference(backward_demodulation,[],[f1324,f1394])).
% 1.49/0.61  fof(f1394,plain,(
% 1.49/0.61    k1_xboole_0 = sK3 | (~spl6_4 | ~spl6_9)),
% 1.49/0.61    inference(forward_demodulation,[],[f1393,f85])).
% 1.49/0.61  fof(f1393,plain,(
% 1.49/0.61    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl6_4 | ~spl6_9)),
% 1.49/0.61    inference(forward_demodulation,[],[f155,f109])).
% 1.49/0.61  fof(f155,plain,(
% 1.49/0.61    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl6_9),
% 1.49/0.61    inference(avatar_component_clause,[],[f153])).
% 1.49/0.61  fof(f1324,plain,(
% 1.49/0.61    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl6_5 | spl6_32)),
% 1.49/0.61    inference(forward_demodulation,[],[f488,f114])).
% 1.49/0.61  fof(f488,plain,(
% 1.49/0.61    sK0 != k1_relset_1(sK0,sK2,sK3) | spl6_32),
% 1.49/0.61    inference(avatar_component_clause,[],[f486])).
% 1.49/0.61  fof(f486,plain,(
% 1.49/0.61    spl6_32 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.49/0.61  fof(f1480,plain,(
% 1.49/0.61    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_9)),
% 1.49/0.61    inference(backward_demodulation,[],[f1438,f1474])).
% 1.49/0.61  fof(f1474,plain,(
% 1.49/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_9)),
% 1.49/0.61    inference(resolution,[],[f1473,f56])).
% 1.49/0.61  fof(f1473,plain,(
% 1.49/0.61    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_9)),
% 1.49/0.61    inference(resolution,[],[f1472,f66])).
% 1.49/0.61  fof(f1472,plain,(
% 1.49/0.61    m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_4 | ~spl6_5 | ~spl6_9)),
% 1.49/0.61    inference(subsumption_resolution,[],[f1471,f1433])).
% 1.49/0.61  fof(f1433,plain,(
% 1.49/0.61    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl6_4 | ~spl6_9)),
% 1.49/0.61    inference(backward_demodulation,[],[f1149,f1394])).
% 1.49/0.61  fof(f1149,plain,(
% 1.49/0.61    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_4),
% 1.49/0.61    inference(forward_demodulation,[],[f1148,f85])).
% 1.49/0.61  fof(f1148,plain,(
% 1.49/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_4),
% 1.49/0.61    inference(forward_demodulation,[],[f51,f109])).
% 1.49/0.61  fof(f1471,plain,(
% 1.49/0.61    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_4 | ~spl6_5 | ~spl6_9)),
% 1.49/0.61    inference(forward_demodulation,[],[f1470,f85])).
% 1.49/0.61  fof(f1470,plain,(
% 1.49/0.61    m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_4 | ~spl6_5 | ~spl6_9)),
% 1.49/0.61    inference(superposition,[],[f73,f1435])).
% 1.49/0.61  fof(f1435,plain,(
% 1.49/0.61    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_9)),
% 1.49/0.61    inference(backward_demodulation,[],[f1170,f1394])).
% 1.49/0.61  fof(f1170,plain,(
% 1.49/0.61    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_4 | ~spl6_5)),
% 1.49/0.61    inference(forward_demodulation,[],[f1169,f114])).
% 1.49/0.61  fof(f1169,plain,(
% 1.49/0.61    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl6_4),
% 1.49/0.61    inference(forward_demodulation,[],[f135,f109])).
% 1.49/0.61  fof(f135,plain,(
% 1.49/0.61    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.49/0.61    inference(resolution,[],[f51,f72])).
% 1.49/0.61  fof(f72,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f27])).
% 1.49/0.61  fof(f27,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.61    inference(ennf_transformation,[],[f13])).
% 1.49/0.61  fof(f13,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.49/0.61  fof(f73,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f28])).
% 1.49/0.61  fof(f28,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.61    inference(ennf_transformation,[],[f12])).
% 1.49/0.61  fof(f12,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.49/0.61  fof(f1438,plain,(
% 1.49/0.61    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_9)),
% 1.49/0.61    inference(backward_demodulation,[],[f1327,f1394])).
% 1.49/0.61  fof(f1327,plain,(
% 1.49/0.61    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3) | ~spl6_5),
% 1.49/0.61    inference(forward_demodulation,[],[f615,f114])).
% 2.07/0.63  fof(f615,plain,(
% 2.07/0.63    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 2.07/0.63    inference(resolution,[],[f608,f72])).
% 2.07/0.63  fof(f838,plain,(
% 2.07/0.63    spl6_2 | ~spl6_7 | ~spl6_32),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f837])).
% 2.07/0.63  fof(f837,plain,(
% 2.07/0.63    $false | (spl6_2 | ~spl6_7 | ~spl6_32)),
% 2.07/0.63    inference(subsumption_resolution,[],[f753,f626])).
% 2.07/0.63  fof(f626,plain,(
% 2.07/0.63    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl6_2 | ~spl6_32)),
% 2.07/0.63    inference(backward_demodulation,[],[f101,f624])).
% 2.07/0.63  fof(f624,plain,(
% 2.07/0.63    k1_xboole_0 = sK2 | (spl6_2 | ~spl6_32)),
% 2.07/0.63    inference(subsumption_resolution,[],[f619,f101])).
% 2.07/0.63  fof(f619,plain,(
% 2.07/0.63    k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | ~spl6_32),
% 2.07/0.63    inference(subsumption_resolution,[],[f613,f487])).
% 2.07/0.63  fof(f487,plain,(
% 2.07/0.63    sK0 = k1_relset_1(sK0,sK2,sK3) | ~spl6_32),
% 2.07/0.63    inference(avatar_component_clause,[],[f486])).
% 2.07/0.63  fof(f613,plain,(
% 2.07/0.63    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2)),
% 2.07/0.63    inference(resolution,[],[f608,f77])).
% 2.07/0.63  fof(f77,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f48])).
% 2.07/0.63  fof(f48,plain,(
% 2.07/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.63    inference(nnf_transformation,[],[f31])).
% 2.07/0.63  fof(f31,plain,(
% 2.07/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.63    inference(flattening,[],[f30])).
% 2.07/0.63  fof(f30,plain,(
% 2.07/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.63    inference(ennf_transformation,[],[f15])).
% 2.07/0.63  fof(f15,axiom,(
% 2.07/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.07/0.63  fof(f101,plain,(
% 2.07/0.63    ~v1_funct_2(sK3,sK0,sK2) | spl6_2),
% 2.07/0.63    inference(avatar_component_clause,[],[f99])).
% 2.07/0.63  fof(f99,plain,(
% 2.07/0.63    spl6_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.07/0.63  fof(f753,plain,(
% 2.07/0.63    v1_funct_2(sK3,sK0,k1_xboole_0) | (spl6_2 | ~spl6_7 | ~spl6_32)),
% 2.07/0.63    inference(backward_demodulation,[],[f50,f747])).
% 2.07/0.63  fof(f747,plain,(
% 2.07/0.63    k1_xboole_0 = sK1 | (spl6_2 | ~spl6_7 | ~spl6_32)),
% 2.07/0.63    inference(forward_demodulation,[],[f128,f624])).
% 2.07/0.63  fof(f128,plain,(
% 2.07/0.63    sK1 = sK2 | ~spl6_7),
% 2.07/0.63    inference(avatar_component_clause,[],[f126])).
% 2.07/0.63  fof(f126,plain,(
% 2.07/0.63    spl6_7 <=> sK1 = sK2),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.07/0.63  fof(f50,plain,(
% 2.07/0.63    v1_funct_2(sK3,sK0,sK1)),
% 2.07/0.63    inference(cnf_transformation,[],[f37])).
% 2.07/0.63  fof(f675,plain,(
% 2.07/0.63    spl6_2 | spl6_6 | ~spl6_32),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f674])).
% 2.07/0.63  fof(f674,plain,(
% 2.07/0.63    $false | (spl6_2 | spl6_6 | ~spl6_32)),
% 2.07/0.63    inference(subsumption_resolution,[],[f632,f55])).
% 2.07/0.63  fof(f55,plain,(
% 2.07/0.63    v1_xboole_0(k1_xboole_0)),
% 2.07/0.63    inference(cnf_transformation,[],[f3])).
% 2.07/0.63  fof(f3,axiom,(
% 2.07/0.63    v1_xboole_0(k1_xboole_0)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.07/0.63  fof(f632,plain,(
% 2.07/0.63    ~v1_xboole_0(k1_xboole_0) | (spl6_2 | spl6_6 | ~spl6_32)),
% 2.07/0.63    inference(backward_demodulation,[],[f131,f624])).
% 2.07/0.63  fof(f131,plain,(
% 2.07/0.63    ~v1_xboole_0(sK2) | spl6_6),
% 2.07/0.63    inference(resolution,[],[f130,f57])).
% 2.07/0.63  fof(f57,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f23])).
% 2.07/0.63  fof(f23,plain,(
% 2.07/0.63    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.07/0.63    inference(ennf_transformation,[],[f18])).
% 2.07/0.63  fof(f18,plain,(
% 2.07/0.63    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.07/0.63    inference(unused_predicate_definition_removal,[],[f1])).
% 2.07/0.63  fof(f1,axiom,(
% 2.07/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.07/0.63  fof(f130,plain,(
% 2.07/0.63    r2_hidden(sK4(sK2,sK1),sK2) | spl6_6),
% 2.07/0.63    inference(resolution,[],[f124,f64])).
% 2.07/0.63  fof(f64,plain,(
% 2.07/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f44])).
% 2.07/0.63  fof(f44,plain,(
% 2.07/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 2.07/0.63  fof(f43,plain,(
% 2.07/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.07/0.63    introduced(choice_axiom,[])).
% 2.07/0.63  fof(f42,plain,(
% 2.07/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.63    inference(rectify,[],[f41])).
% 2.07/0.63  fof(f41,plain,(
% 2.07/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.63    inference(nnf_transformation,[],[f25])).
% 2.07/0.63  fof(f25,plain,(
% 2.07/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.07/0.63    inference(ennf_transformation,[],[f2])).
% 2.07/0.63  fof(f2,axiom,(
% 2.07/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.07/0.63  fof(f124,plain,(
% 2.07/0.63    ~r1_tarski(sK2,sK1) | spl6_6),
% 2.07/0.63    inference(avatar_component_clause,[],[f122])).
% 2.07/0.63  fof(f122,plain,(
% 2.07/0.63    spl6_6 <=> r1_tarski(sK2,sK1)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.07/0.63  fof(f610,plain,(
% 2.07/0.63    spl6_3),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f609])).
% 2.07/0.63  fof(f609,plain,(
% 2.07/0.63    $false | spl6_3),
% 2.07/0.63    inference(subsumption_resolution,[],[f608,f105])).
% 2.07/0.63  fof(f105,plain,(
% 2.07/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_3),
% 2.07/0.63    inference(avatar_component_clause,[],[f103])).
% 2.07/0.63  fof(f103,plain,(
% 2.07/0.63    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.07/0.63  fof(f502,plain,(
% 2.07/0.63    ~spl6_3 | spl6_4 | spl6_32),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f501])).
% 2.07/0.63  fof(f501,plain,(
% 2.07/0.63    $false | (~spl6_3 | spl6_4 | spl6_32)),
% 2.07/0.63    inference(subsumption_resolution,[],[f500,f488])).
% 2.07/0.63  fof(f500,plain,(
% 2.07/0.63    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl6_3 | spl6_4)),
% 2.07/0.63    inference(forward_demodulation,[],[f496,f141])).
% 2.07/0.63  fof(f141,plain,(
% 2.07/0.63    sK0 = k1_relat_1(sK3) | spl6_4),
% 2.07/0.63    inference(forward_demodulation,[],[f135,f140])).
% 2.07/0.63  fof(f140,plain,(
% 2.07/0.63    sK0 = k1_relset_1(sK0,sK1,sK3) | spl6_4),
% 2.07/0.63    inference(subsumption_resolution,[],[f139,f110])).
% 2.07/0.63  fof(f110,plain,(
% 2.07/0.63    k1_xboole_0 != sK1 | spl6_4),
% 2.07/0.63    inference(avatar_component_clause,[],[f108])).
% 2.07/0.63  fof(f139,plain,(
% 2.07/0.63    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.07/0.63    inference(subsumption_resolution,[],[f132,f50])).
% 2.07/0.63  fof(f132,plain,(
% 2.07/0.63    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.07/0.63    inference(resolution,[],[f51,f75])).
% 2.07/0.63  fof(f75,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.07/0.63    inference(cnf_transformation,[],[f48])).
% 2.07/0.63  fof(f496,plain,(
% 2.07/0.63    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl6_3),
% 2.07/0.63    inference(resolution,[],[f104,f72])).
% 2.07/0.63  fof(f104,plain,(
% 2.07/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_3),
% 2.07/0.63    inference(avatar_component_clause,[],[f103])).
% 2.07/0.63  fof(f129,plain,(
% 2.07/0.63    ~spl6_6 | spl6_7),
% 2.07/0.63    inference(avatar_split_clause,[],[f120,f126,f122])).
% 2.07/0.63  fof(f120,plain,(
% 2.07/0.63    sK1 = sK2 | ~r1_tarski(sK2,sK1)),
% 2.07/0.63    inference(resolution,[],[f52,f62])).
% 2.07/0.63  fof(f62,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f40])).
% 2.07/0.63  fof(f117,plain,(
% 2.07/0.63    spl6_1),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f116])).
% 2.07/0.63  fof(f116,plain,(
% 2.07/0.63    $false | spl6_1),
% 2.07/0.63    inference(subsumption_resolution,[],[f97,f49])).
% 2.07/0.63  fof(f49,plain,(
% 2.07/0.63    v1_funct_1(sK3)),
% 2.07/0.63    inference(cnf_transformation,[],[f37])).
% 2.07/0.63  fof(f97,plain,(
% 2.07/0.63    ~v1_funct_1(sK3) | spl6_1),
% 2.07/0.63    inference(avatar_component_clause,[],[f95])).
% 2.07/0.63  fof(f95,plain,(
% 2.07/0.63    spl6_1 <=> v1_funct_1(sK3)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.07/0.63  fof(f115,plain,(
% 2.07/0.63    ~spl6_4 | spl6_5),
% 2.07/0.63    inference(avatar_split_clause,[],[f53,f112,f108])).
% 2.07/0.63  fof(f53,plain,(
% 2.07/0.63    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.07/0.63    inference(cnf_transformation,[],[f37])).
% 2.07/0.63  fof(f106,plain,(
% 2.07/0.63    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 2.07/0.63    inference(avatar_split_clause,[],[f54,f103,f99,f95])).
% 2.07/0.63  fof(f54,plain,(
% 2.07/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.07/0.63    inference(cnf_transformation,[],[f37])).
% 2.07/0.63  % SZS output end Proof for theBenchmark
% 2.07/0.63  % (6541)------------------------------
% 2.07/0.63  % (6541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (6541)Termination reason: Refutation
% 2.07/0.63  
% 2.07/0.63  % (6541)Memory used [KB]: 11129
% 2.07/0.63  % (6541)Time elapsed: 0.183 s
% 2.07/0.63  % (6541)------------------------------
% 2.07/0.63  % (6541)------------------------------
% 2.07/0.63  % (6532)Success in time 0.268 s
%------------------------------------------------------------------------------
