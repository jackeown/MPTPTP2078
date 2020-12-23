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
% DateTime   : Thu Dec  3 13:02:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 633 expanded)
%              Number of leaves         :   37 ( 182 expanded)
%              Depth                    :   17
%              Number of atoms          :  714 (2838 expanded)
%              Number of equality atoms :  114 ( 577 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1955,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f185,f575,f745,f756,f778,f779,f1193,f1198,f1199,f1237,f1422,f1434,f1435,f1442,f1444,f1503,f1747,f1859,f1954])).

fof(f1954,plain,
    ( spl4_3
    | ~ spl4_13
    | ~ spl4_80 ),
    inference(avatar_contradiction_clause,[],[f1953])).

fof(f1953,plain,
    ( $false
    | spl4_3
    | ~ spl4_13
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f1952,f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1952,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_13
    | ~ spl4_80 ),
    inference(forward_demodulation,[],[f1951,f1764])).

fof(f1764,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_80 ),
    inference(resolution,[],[f1748,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f1748,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_80 ),
    inference(resolution,[],[f1339,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1339,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1338,plain,
    ( spl4_80
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1951,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1950,f317])).

fof(f317,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_13 ),
    inference(resolution,[],[f303,f69])).

fof(f303,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_13 ),
    inference(resolution,[],[f275,f83])).

fof(f275,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f273,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f273,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f50,f167])).

fof(f167,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f41])).

fof(f41,plain,
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

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f1950,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1949,f90])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1949,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_3
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f102,f167])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1859,plain,
    ( spl4_2
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_80 ),
    inference(avatar_contradiction_clause,[],[f1858])).

fof(f1858,plain,
    ( $false
    | spl4_2
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f1833,f1511])).

fof(f1511,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f335,f290])).

fof(f290,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f335,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f274,f317])).

fof(f274,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f49,f167])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f1833,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_80 ),
    inference(backward_demodulation,[],[f1614,f1764])).

fof(f1614,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_13
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1613,f317])).

fof(f1613,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_13
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f316,f290])).

fof(f316,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f98,f167])).

fof(f98,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1747,plain,
    ( ~ spl4_6
    | ~ spl4_13
    | ~ spl4_32
    | ~ spl4_33
    | spl4_80 ),
    inference(avatar_contradiction_clause,[],[f1746])).

fof(f1746,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_32
    | ~ spl4_33
    | spl4_80 ),
    inference(subsumption_resolution,[],[f1745,f1340])).

fof(f1340,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_80 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1745,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f1744,f90])).

fof(f1744,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1743,f375])).

fof(f375,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl4_32
  <=> v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1743,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1737,f380])).

fof(f380,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl4_33
  <=> v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1737,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(superposition,[],[f77,f1701])).

fof(f1701,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1234,f317])).

fof(f1234,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f966,f167])).

fof(f966,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f123,f696])).

fof(f696,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f694,f50])).

fof(f694,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f52,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_6
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1503,plain,
    ( spl4_25
    | spl4_26
    | ~ spl4_27
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f1502,f165,f296,f292,f288])).

fof(f292,plain,
    ( spl4_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f296,plain,
    ( spl4_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1502,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1492,f89])).

fof(f1492,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f1228,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

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

fof(f1228,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f49,f167])).

fof(f1444,plain,
    ( ~ spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f1443,f126,f113])).

fof(f113,plain,
    ( spl4_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f126,plain,
    ( spl4_7
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1443,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1440,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f1440,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f1442,plain,
    ( ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f1441,f121,f113])).

fof(f1441,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1439,f48])).

fof(f1439,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1435,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f1427,f92,f113])).

fof(f92,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1427,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1434,plain,
    ( ~ spl4_4
    | spl4_8 ),
    inference(avatar_split_clause,[],[f1426,f131,f113])).

fof(f131,plain,
    ( spl4_8
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1426,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1422,plain,
    ( ~ spl4_6
    | ~ spl4_13
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_33
    | spl4_44 ),
    inference(avatar_contradiction_clause,[],[f1421])).

fof(f1421,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_33
    | spl4_44 ),
    inference(subsumption_resolution,[],[f1381,f1302])).

fof(f1302,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_13
    | ~ spl4_26
    | spl4_44 ),
    inference(forward_demodulation,[],[f1301,f90])).

fof(f1301,plain,
    ( ! [X0] : ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl4_13
    | ~ spl4_26
    | spl4_44 ),
    inference(subsumption_resolution,[],[f1292,f82])).

% (16554)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1292,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl4_13
    | ~ spl4_26
    | spl4_44 ),
    inference(resolution,[],[f1289,f81])).

% (16558)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f1289,plain,
    ( ~ v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_26
    | spl4_44 ),
    inference(forward_demodulation,[],[f1288,f294])).

fof(f294,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f292])).

fof(f1288,plain,
    ( ~ v1_partfun1(k2_funct_1(sK2),k1_xboole_0)
    | ~ spl4_13
    | spl4_44 ),
    inference(forward_demodulation,[],[f574,f167])).

fof(f574,plain,
    ( ~ v1_partfun1(k2_funct_1(sK2),sK1)
    | spl4_44 ),
    inference(avatar_component_clause,[],[f572])).

fof(f572,plain,
    ( spl4_44
  <=> v1_partfun1(k2_funct_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1381,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f1380,f90])).

fof(f1380,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1379,f375])).

fof(f1379,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_26
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1373,f380])).

fof(f1373,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_26 ),
    inference(superposition,[],[f77,f1360])).

fof(f1360,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f1234,f294])).

fof(f1237,plain,
    ( ~ spl4_13
    | spl4_27 ),
    inference(avatar_contradiction_clause,[],[f1236])).

fof(f1236,plain,
    ( $false
    | ~ spl4_13
    | spl4_27 ),
    inference(subsumption_resolution,[],[f1235,f298])).

fof(f298,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f296])).

fof(f1235,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1229,f89])).

fof(f1229,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f50,f167])).

fof(f1199,plain,
    ( spl4_13
    | spl4_14 ),
    inference(avatar_split_clause,[],[f647,f169,f165])).

fof(f169,plain,
    ( spl4_14
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f647,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f638,f49])).

fof(f638,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1198,plain,
    ( ~ spl4_1
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f1197])).

fof(f1197,plain,
    ( $false
    | ~ spl4_1
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1196,f102])).

fof(f1196,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1195,f966])).

fof(f1195,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1194,f133])).

fof(f133,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1194,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1188,f93])).

fof(f93,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1188,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(superposition,[],[f77,f1176])).

fof(f1176,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f128,f1173])).

fof(f1173,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1169,f50])).

fof(f1169,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_14 ),
    inference(superposition,[],[f171,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f171,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f128,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f1193,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f1192])).

fof(f1192,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1191,f98])).

fof(f1191,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1190,f966])).

fof(f1190,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1189,f133])).

fof(f1189,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1187,f93])).

fof(f1187,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(superposition,[],[f76,f1176])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f779,plain,
    ( ~ spl4_46
    | spl4_33
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f764,f355,f378,f618])).

fof(f618,plain,
    ( spl4_46
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f355,plain,
    ( spl4_28
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f764,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl4_28 ),
    inference(resolution,[],[f356,f57])).

fof(f356,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f355])).

fof(f778,plain,
    ( ~ spl4_46
    | spl4_32
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f763,f355,f373,f618])).

fof(f763,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl4_28 ),
    inference(resolution,[],[f356,f56])).

fof(f756,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | spl4_28 ),
    inference(subsumption_resolution,[],[f746,f78])).

fof(f746,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_28 ),
    inference(resolution,[],[f357,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f357,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f355])).

fof(f745,plain,(
    spl4_46 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | spl4_46 ),
    inference(subsumption_resolution,[],[f737,f71])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( v2_funct_1(sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v2_funct_1(sK3)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_1)).

fof(f737,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_46 ),
    inference(resolution,[],[f634,f70])).

fof(f70,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f634,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | spl4_46 ),
    inference(subsumption_resolution,[],[f625,f78])).

fof(f625,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl4_46 ),
    inference(resolution,[],[f620,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f620,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl4_46 ),
    inference(avatar_component_clause,[],[f618])).

fof(f575,plain,
    ( ~ spl4_3
    | ~ spl4_44
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f570,f96,f92,f572,f100])).

fof(f570,plain,
    ( ~ v1_partfun1(k2_funct_1(sK2),sK1)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f568,f93])).

fof(f568,plain,
    ( ~ v1_partfun1(k2_funct_1(sK2),sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_2 ),
    inference(resolution,[],[f98,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

% (16542)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f185,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f177,f115])).

fof(f115,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f177,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f73])).

fof(f103,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f100,f96,f92])).

fof(f53,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (16551)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (16557)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.46  % (16539)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (16539)Refutation not found, incomplete strategy% (16539)------------------------------
% 0.21/0.47  % (16539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16546)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (16539)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (16539)Memory used [KB]: 10618
% 0.21/0.47  % (16539)Time elapsed: 0.062 s
% 0.21/0.47  % (16539)------------------------------
% 0.21/0.47  % (16539)------------------------------
% 0.21/0.47  % (16538)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (16549)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (16543)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (16547)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (16552)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (16550)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (16545)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (16548)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (16540)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (16544)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (16557)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1955,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f103,f185,f575,f745,f756,f778,f779,f1193,f1198,f1199,f1237,f1422,f1434,f1435,f1442,f1444,f1503,f1747,f1859,f1954])).
% 0.21/0.50  fof(f1954,plain,(
% 0.21/0.50    spl4_3 | ~spl4_13 | ~spl4_80),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1953])).
% 0.21/0.50  fof(f1953,plain,(
% 0.21/0.50    $false | (spl4_3 | ~spl4_13 | ~spl4_80)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1952,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f1952,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_13 | ~spl4_80)),
% 0.21/0.50    inference(forward_demodulation,[],[f1951,f1764])).
% 0.21/0.50  fof(f1764,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl4_80),
% 0.21/0.50    inference(resolution,[],[f1748,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.50  fof(f1748,plain,(
% 0.21/0.50    r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) | ~spl4_80),
% 0.21/0.50    inference(resolution,[],[f1339,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.50    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f1339,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_80),
% 0.21/0.50    inference(avatar_component_clause,[],[f1338])).
% 0.21/0.50  fof(f1338,plain,(
% 0.21/0.50    spl4_80 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 0.21/0.50  fof(f1951,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f1950,f317])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl4_13),
% 0.21/0.50    inference(resolution,[],[f303,f69])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    r1_tarski(sK2,k1_xboole_0) | ~spl4_13),
% 0.21/0.50    inference(resolution,[],[f275,f83])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_13),
% 0.21/0.50    inference(forward_demodulation,[],[f273,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    inference(flattening,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_13),
% 0.21/0.50    inference(backward_demodulation,[],[f50,f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl4_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl4_13 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f18])).
% 0.21/0.50  fof(f18,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.50  fof(f1950,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f1949,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f1949,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_3 | ~spl4_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f102,f167])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl4_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f1859,plain,(
% 0.21/0.50    spl4_2 | ~spl4_13 | ~spl4_25 | ~spl4_80),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1858])).
% 0.21/0.50  fof(f1858,plain,(
% 0.21/0.50    $false | (spl4_2 | ~spl4_13 | ~spl4_25 | ~spl4_80)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1833,f1511])).
% 0.21/0.50  fof(f1511,plain,(
% 0.21/0.50    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_13 | ~spl4_25)),
% 0.21/0.50    inference(backward_demodulation,[],[f335,f290])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl4_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f288])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    spl4_25 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~spl4_13),
% 0.21/0.50    inference(backward_demodulation,[],[f274,f317])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl4_13),
% 0.21/0.50    inference(backward_demodulation,[],[f49,f167])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f1833,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_13 | ~spl4_25 | ~spl4_80)),
% 0.21/0.50    inference(backward_demodulation,[],[f1614,f1764])).
% 0.21/0.50  fof(f1614,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_13 | ~spl4_25)),
% 0.21/0.50    inference(forward_demodulation,[],[f1613,f317])).
% 0.21/0.50  fof(f1613,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_13 | ~spl4_25)),
% 0.21/0.50    inference(forward_demodulation,[],[f316,f290])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f98,f167])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f1747,plain,(
% 0.21/0.50    ~spl4_6 | ~spl4_13 | ~spl4_32 | ~spl4_33 | spl4_80),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1746])).
% 0.21/0.50  fof(f1746,plain,(
% 0.21/0.50    $false | (~spl4_6 | ~spl4_13 | ~spl4_32 | ~spl4_33 | spl4_80)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1745,f1340])).
% 0.21/0.50  fof(f1340,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl4_80),
% 0.21/0.50    inference(avatar_component_clause,[],[f1338])).
% 0.21/0.50  fof(f1745,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | ~spl4_13 | ~spl4_32 | ~spl4_33)),
% 0.21/0.50    inference(forward_demodulation,[],[f1744,f90])).
% 0.21/0.50  fof(f1744,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | (~spl4_6 | ~spl4_13 | ~spl4_32 | ~spl4_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1743,f375])).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f373])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    spl4_32 <=> v1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.50  fof(f1743,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_6 | ~spl4_13 | ~spl4_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1737,f380])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~spl4_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f378])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    spl4_33 <=> v1_funct_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.50  fof(f1737,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_6 | ~spl4_13)),
% 0.21/0.50    inference(superposition,[],[f77,f1701])).
% 0.21/0.50  fof(f1701,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_6 | ~spl4_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f1234,f317])).
% 0.21/0.50  fof(f1234,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | (~spl4_6 | ~spl4_13)),
% 0.21/0.50    inference(backward_demodulation,[],[f966,f167])).
% 0.21/0.50  fof(f966,plain,(
% 0.21/0.50    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_6),
% 0.21/0.50    inference(forward_demodulation,[],[f123,f696])).
% 0.21/0.50  fof(f696,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f694,f50])).
% 0.21/0.50  fof(f694,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(superposition,[],[f52,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl4_6 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.50  fof(f1503,plain,(
% 0.21/0.50    spl4_25 | spl4_26 | ~spl4_27 | ~spl4_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f1502,f165,f296,f292,f288])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    spl4_26 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    spl4_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.50  fof(f1502,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | ~spl4_13),
% 0.21/0.50    inference(forward_demodulation,[],[f1492,f89])).
% 0.21/0.50  fof(f1492,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_13),
% 0.21/0.50    inference(resolution,[],[f1228,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f1228,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl4_13),
% 0.21/0.50    inference(backward_demodulation,[],[f49,f167])).
% 0.21/0.50  fof(f1444,plain,(
% 0.21/0.50    ~spl4_4 | spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f1443,f126,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl4_4 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl4_7 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f1443,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1440,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f1440,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f51,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v2_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f1442,plain,(
% 0.21/0.50    ~spl4_4 | spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f1441,f121,f113])).
% 0.21/0.50  fof(f1441,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1439,f48])).
% 0.21/0.50  fof(f1439,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f51,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f1435,plain,(
% 0.21/0.50    ~spl4_4 | spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f1427,f92,f113])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl4_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f1427,plain,(
% 0.21/0.50    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f48,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f1434,plain,(
% 0.21/0.50    ~spl4_4 | spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f1426,f131,f113])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl4_8 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f1426,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f48,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f1422,plain,(
% 0.21/0.50    ~spl4_6 | ~spl4_13 | ~spl4_26 | ~spl4_32 | ~spl4_33 | spl4_44),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1421])).
% 0.21/0.50  fof(f1421,plain,(
% 0.21/0.50    $false | (~spl4_6 | ~spl4_13 | ~spl4_26 | ~spl4_32 | ~spl4_33 | spl4_44)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1381,f1302])).
% 0.21/0.50  fof(f1302,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_13 | ~spl4_26 | spl4_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f1301,f90])).
% 0.21/0.50  fof(f1301,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl4_13 | ~spl4_26 | spl4_44)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1292,f82])).
% 0.21/0.50  % (16554)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f1292,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~v1_xboole_0(k1_xboole_0)) ) | (~spl4_13 | ~spl4_26 | spl4_44)),
% 0.21/0.50    inference(resolution,[],[f1289,f81])).
% 0.21/0.50  % (16558)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.50  fof(f1289,plain,(
% 0.21/0.50    ~v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl4_13 | ~spl4_26 | spl4_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f1288,f294])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl4_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f292])).
% 0.21/0.50  fof(f1288,plain,(
% 0.21/0.50    ~v1_partfun1(k2_funct_1(sK2),k1_xboole_0) | (~spl4_13 | spl4_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f574,f167])).
% 0.21/0.50  fof(f574,plain,(
% 0.21/0.50    ~v1_partfun1(k2_funct_1(sK2),sK1) | spl4_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f572])).
% 0.21/0.50  fof(f572,plain,(
% 0.21/0.50    spl4_44 <=> v1_partfun1(k2_funct_1(sK2),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.50  fof(f1381,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | ~spl4_13 | ~spl4_26 | ~spl4_32 | ~spl4_33)),
% 0.21/0.50    inference(forward_demodulation,[],[f1380,f90])).
% 0.21/0.50  fof(f1380,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | (~spl4_6 | ~spl4_13 | ~spl4_26 | ~spl4_32 | ~spl4_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1379,f375])).
% 0.21/0.50  fof(f1379,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_6 | ~spl4_13 | ~spl4_26 | ~spl4_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1373,f380])).
% 0.21/0.50  fof(f1373,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_6 | ~spl4_13 | ~spl4_26)),
% 0.21/0.50    inference(superposition,[],[f77,f1360])).
% 0.21/0.50  fof(f1360,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_6 | ~spl4_13 | ~spl4_26)),
% 0.21/0.50    inference(forward_demodulation,[],[f1234,f294])).
% 0.21/0.50  fof(f1237,plain,(
% 0.21/0.50    ~spl4_13 | spl4_27),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1236])).
% 0.21/0.50  fof(f1236,plain,(
% 0.21/0.50    $false | (~spl4_13 | spl4_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1235,f298])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl4_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f296])).
% 0.21/0.50  fof(f1235,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_13),
% 0.21/0.50    inference(forward_demodulation,[],[f1229,f89])).
% 0.21/0.50  fof(f1229,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_13),
% 0.21/0.50    inference(backward_demodulation,[],[f50,f167])).
% 0.21/0.50  fof(f1199,plain,(
% 0.21/0.50    spl4_13 | spl4_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f647,f169,f165])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl4_14 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.50  fof(f647,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f638,f49])).
% 0.21/0.50  fof(f638,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(resolution,[],[f50,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f1198,plain,(
% 0.21/0.50    ~spl4_1 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1197])).
% 0.21/0.50  fof(f1197,plain,(
% 0.21/0.50    $false | (~spl4_1 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1196,f102])).
% 0.21/0.51  fof(f1196,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f1195,f966])).
% 0.21/0.51  fof(f1195,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl4_1 | ~spl4_7 | ~spl4_8 | ~spl4_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1194,f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl4_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f1194,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_7 | ~spl4_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1188,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK2)) | ~spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f1188,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_7 | ~spl4_14)),
% 0.21/0.51    inference(superposition,[],[f77,f1176])).
% 0.21/0.51  fof(f1176,plain,(
% 0.21/0.51    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl4_7 | ~spl4_14)),
% 0.21/0.51    inference(backward_demodulation,[],[f128,f1173])).
% 0.21/0.51  fof(f1173,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | ~spl4_14),
% 0.21/0.51    inference(subsumption_resolution,[],[f1169,f50])).
% 0.21/0.51  fof(f1169,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_14),
% 0.21/0.51    inference(superposition,[],[f171,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f1193,plain,(
% 0.21/0.51    ~spl4_1 | spl4_2 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1192])).
% 0.21/0.51  fof(f1192,plain,(
% 0.21/0.51    $false | (~spl4_1 | spl4_2 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1191,f98])).
% 0.21/0.51  fof(f1191,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f1190,f966])).
% 0.21/0.51  fof(f1190,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl4_1 | ~spl4_7 | ~spl4_8 | ~spl4_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1189,f133])).
% 0.21/0.51  fof(f1189,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_7 | ~spl4_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1187,f93])).
% 0.21/0.51  fof(f1187,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_7 | ~spl4_14)),
% 0.21/0.51    inference(superposition,[],[f76,f1176])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f779,plain,(
% 0.21/0.51    ~spl4_46 | spl4_33 | ~spl4_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f764,f355,f378,f618])).
% 0.21/0.51  fof(f618,plain,(
% 0.21/0.51    spl4_46 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    spl4_28 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.51  fof(f764,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~spl4_28),
% 0.21/0.51    inference(resolution,[],[f356,f57])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    v1_relat_1(k1_xboole_0) | ~spl4_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f355])).
% 0.21/0.51  fof(f778,plain,(
% 0.21/0.51    ~spl4_46 | spl4_32 | ~spl4_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f763,f355,f373,f618])).
% 0.21/0.51  fof(f763,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~spl4_28),
% 0.21/0.51    inference(resolution,[],[f356,f56])).
% 0.21/0.51  fof(f756,plain,(
% 0.21/0.51    spl4_28),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f755])).
% 0.21/0.51  fof(f755,plain,(
% 0.21/0.51    $false | spl4_28),
% 0.21/0.51    inference(subsumption_resolution,[],[f746,f78])).
% 0.21/0.51  fof(f746,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_28),
% 0.21/0.51    inference(resolution,[],[f357,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    ~v1_relat_1(k1_xboole_0) | spl4_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f355])).
% 0.21/0.51  fof(f745,plain,(
% 0.21/0.51    spl4_46),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f744])).
% 0.21/0.51  fof(f744,plain,(
% 0.21/0.51    $false | spl4_46),
% 0.21/0.51    inference(subsumption_resolution,[],[f737,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v2_funct_1(sK3) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ? [X0] : (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(sK3) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ? [X0] : (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_1)).
% 0.21/0.51  fof(f737,plain,(
% 0.21/0.51    ~v1_funct_1(sK3) | spl4_46),
% 0.21/0.51    inference(resolution,[],[f634,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    v1_relat_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f634,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0)) ) | spl4_46),
% 0.21/0.51    inference(subsumption_resolution,[],[f625,f78])).
% 0.21/0.51  fof(f625,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | spl4_46),
% 0.21/0.51    inference(resolution,[],[f620,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).
% 0.21/0.51  fof(f620,plain,(
% 0.21/0.51    ~v1_funct_1(k1_xboole_0) | spl4_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f618])).
% 0.21/0.51  fof(f575,plain,(
% 0.21/0.51    ~spl4_3 | ~spl4_44 | ~spl4_1 | spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f570,f96,f92,f572,f100])).
% 0.21/0.51  fof(f570,plain,(
% 0.21/0.51    ~v1_partfun1(k2_funct_1(sK2),sK1) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_1 | spl4_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f568,f93])).
% 0.21/0.51  fof(f568,plain,(
% 0.21/0.51    ~v1_partfun1(k2_funct_1(sK2),sK1) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_2),
% 0.21/0.51    inference(resolution,[],[f98,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  % (16542)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f184])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    $false | spl4_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f177,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f50,f73])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f100,f96,f92])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (16557)------------------------------
% 0.21/0.51  % (16557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16557)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (16557)Memory used [KB]: 6780
% 0.21/0.51  % (16557)Time elapsed: 0.088 s
% 0.21/0.51  % (16557)------------------------------
% 0.21/0.51  % (16557)------------------------------
% 0.21/0.51  % (16553)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (16537)Success in time 0.154 s
%------------------------------------------------------------------------------
