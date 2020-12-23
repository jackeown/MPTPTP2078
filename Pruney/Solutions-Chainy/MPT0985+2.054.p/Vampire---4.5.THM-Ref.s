%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:07 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  238 (2202 expanded)
%              Number of leaves         :   37 ( 583 expanded)
%              Depth                    :   19
%              Number of atoms          :  750 (12754 expanded)
%              Number of equality atoms :  162 (1842 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f191,f264,f266,f416,f541,f547,f589,f643,f651,f660,f846,f1406,f1461])).

fof(f1461,plain,
    ( spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f1460])).

fof(f1460,plain,
    ( $false
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f1454,f859])).

fof(f859,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f858,f263])).

fof(f263,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f858,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f588,f257])).

fof(f257,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f588,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl7_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f1454,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f661,f659,f1412,f848,f161])).

fof(f161,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f848,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f847,f263])).

fof(f847,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f642,f257])).

fof(f642,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f640])).

fof(f640,plain,
    ( spl7_28
  <=> v1_funct_2(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f1412,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f1411,f887])).

fof(f887,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f672,f885])).

fof(f885,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f884,f152])).

fof(f152,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f97,f99])).

fof(f99,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f97,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f884,plain,
    ( k6_partfun1(k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f883,f263])).

fof(f883,plain,
    ( k6_partfun1(k1_xboole_0) = k4_relat_1(sK2)
    | ~ spl7_5
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f415,f257])).

fof(f415,plain,
    ( k4_relat_1(sK2) = k6_partfun1(sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl7_14
  <=> k4_relat_1(sK2) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f672,plain,
    ( k4_relat_1(k1_xboole_0) = k2_funct_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f219,f263])).

fof(f219,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f93,f90,f188,f125])).

fof(f125,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f188,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f92,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f81])).

fof(f81,plain,
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

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f37])).

fof(f37,conjecture,(
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

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f93,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f1411,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f1410,f263])).

fof(f1410,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl7_2
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f176,f257])).

fof(f176,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f659,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f657])).

fof(f657,plain,
    ( spl7_30
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f661,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f90,f263])).

fof(f1406,plain,
    ( spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_29 ),
    inference(avatar_contradiction_clause,[],[f1405])).

fof(f1405,plain,
    ( $false
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f1397,f1293])).

fof(f1293,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f96,f1286,f163])).

fof(f163,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f163_D])).

fof(f163_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f1286,plain,
    ( ~ sP4(k1_xboole_0)
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f1122,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP4(X1) ) ),
    inference(general_splitting,[],[f145,f163_D])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f1122,plain,
    ( r2_hidden(sK3(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)),k1_xboole_0)
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f974,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f86,f87])).

fof(f87,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f974,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f812,f885])).

fof(f812,plain,
    ( ~ r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f750,f257])).

fof(f750,plain,
    ( ~ r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(sK1,sK0))
    | spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f545,f263])).

fof(f545,plain,
    ( ~ r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(sK1,sK0))
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f542,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f542,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_3 ),
    inference(forward_demodulation,[],[f180,f219])).

fof(f180,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl7_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f96,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1397,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f838,f139])).

fof(f838,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_29 ),
    inference(backward_demodulation,[],[f747,f826])).

fof(f826,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_29 ),
    inference(backward_demodulation,[],[f676,f825])).

fof(f825,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_29 ),
    inference(forward_demodulation,[],[f647,f263])).

fof(f647,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f646])).

fof(f646,plain,
    ( spl7_29
  <=> k1_xboole_0 = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f676,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f227,f263])).

fof(f227,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f221,f219])).

fof(f221,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f93,f90,f188,f127])).

fof(f127,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f747,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f519,f263])).

fof(f519,plain,(
    r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f188,f450,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f450,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f232,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f232,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(forward_demodulation,[],[f216,f192])).

fof(f192,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f187,f94])).

fof(f94,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f187,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f92,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f216,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f90,f188,f122])).

fof(f122,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f846,plain,
    ( ~ spl7_6
    | spl7_13
    | ~ spl7_29 ),
    inference(avatar_contradiction_clause,[],[f845])).

fof(f845,plain,
    ( $false
    | ~ spl7_6
    | spl7_13
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f834,f152])).

fof(f834,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | ~ spl7_6
    | spl7_13
    | ~ spl7_29 ),
    inference(backward_demodulation,[],[f708,f826])).

fof(f708,plain,
    ( k1_xboole_0 != k6_partfun1(k1_relat_1(k1_xboole_0))
    | ~ spl7_6
    | spl7_13 ),
    inference(backward_demodulation,[],[f411,f263])).

fof(f411,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl7_13
  <=> sK2 = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f660,plain,
    ( spl7_30
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f319,f255,f657])).

fof(f319,plain,
    ( k1_xboole_0 != sK1
    | r1_tarski(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f318,f192])).

fof(f318,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f317,f188])).

fof(f317,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f237,f118])).

fof(f118,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f237,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f188,f186,f132])).

fof(f186,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f92,f142])).

fof(f651,plain,
    ( spl7_29
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f650,f255,f646])).

fof(f650,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_relat_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f348,f231])).

fof(f231,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f217,f219])).

fof(f217,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f90,f188,f123])).

fof(f123,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f348,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[],[f117,f226])).

fof(f226,plain,(
    sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f225,f219])).

fof(f225,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f220,f192])).

fof(f220,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f93,f90,f188,f126])).

fof(f126,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f117,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f643,plain,
    ( spl7_28
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f638,f255,f640])).

fof(f638,plain,
    ( k1_xboole_0 != sK1
    | v1_funct_2(sK2,k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f637,f192])).

fof(f637,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f395,f188])).

fof(f395,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f233,f118])).

fof(f233,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f215,f192])).

fof(f215,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f90,f188,f121])).

fof(f121,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f589,plain,
    ( spl7_20
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f584,f255,f586])).

fof(f584,plain,
    ( k1_xboole_0 != sK1
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(forward_demodulation,[],[f583,f192])).

fof(f583,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f454,f188])).

fof(f454,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f232,f118])).

fof(f547,plain,
    ( ~ spl7_1
    | spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | ~ spl7_1
    | spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f544,f302])).

fof(f302,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f301,f226])).

fof(f301,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f295,f227])).

fof(f295,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f197,f231,f122])).

fof(f197,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f196,f188])).

fof(f196,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f195,f90])).

fof(f195,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f194,f93])).

fof(f194,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(superposition,[],[f171,f125])).

fof(f171,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f544,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_1
    | spl7_3
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f197,f237,f253,f304,f542,f150])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f304,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f303,f226])).

fof(f303,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f294,f227])).

fof(f294,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f197,f231,f121])).

fof(f253,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl7_4
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f541,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_4 ),
    inference(subsumption_resolution,[],[f538,f302])).

fof(f538,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_1
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f197,f237,f206,f253,f304,f148])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f206,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f205,f188])).

fof(f205,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_relat_1(sK2)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f204,f90])).

fof(f204,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f199,f93])).

fof(f199,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_2 ),
    inference(superposition,[],[f176,f125])).

fof(f416,plain,
    ( ~ spl7_13
    | spl7_14 ),
    inference(avatar_split_clause,[],[f407,f413,f409])).

fof(f407,plain,
    ( k4_relat_1(sK2) = k6_partfun1(sK1)
    | sK2 != k6_partfun1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f406,f192])).

fof(f406,plain,
    ( sK1 != k2_relat_1(sK2)
    | k4_relat_1(sK2) = k6_partfun1(sK1)
    | sK2 != k6_partfun1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f405,f156])).

fof(f156,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f105,f99])).

fof(f105,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f405,plain,
    ( k4_relat_1(sK2) = k6_partfun1(sK1)
    | sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f404,f219])).

fof(f404,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) ),
    inference(subsumption_resolution,[],[f403,f188])).

fof(f403,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f402,f90])).

fof(f402,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f401,f154])).

fof(f154,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f101,f99])).

fof(f101,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f401,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f400,f153])).

fof(f153,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f102,f99])).

fof(f102,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f400,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f398,f93])).

fof(f398,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(k6_partfun1(sK1))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f159,f224])).

fof(f224,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f223,f192])).

fof(f223,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f188,f157])).

fof(f157,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f112,f99])).

fof(f112,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f159,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f130,f99])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f266,plain,
    ( ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f265,f255,f251])).

fof(f265,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f241,f188])).

fof(f241,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f117,f192])).

fof(f264,plain,
    ( spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f259,f255,f261])).

fof(f259,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f240,f188])).

fof(f240,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f116,f192])).

fof(f116,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f191,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f188,f182])).

fof(f182,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f90,f172,f124])).

fof(f124,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f172,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f170])).

fof(f181,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f95,f178,f174,f170])).

fof(f95,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:27:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (16434)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (16441)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (16433)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (16440)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (16449)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (16454)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (16438)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (16437)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (16435)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (16459)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (16446)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (16447)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (16445)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (16448)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (16470)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (16468)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (16450)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (16443)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (16450)Refutation not found, incomplete strategy% (16450)------------------------------
% 0.21/0.54  % (16450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16450)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16450)Memory used [KB]: 10746
% 0.21/0.54  % (16450)Time elapsed: 0.129 s
% 0.21/0.54  % (16450)------------------------------
% 0.21/0.54  % (16450)------------------------------
% 0.21/0.54  % (16469)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (16436)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (16466)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (16453)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (16452)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (16442)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (16464)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (16439)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (16451)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (16444)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (16461)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.59  % (16457)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.82/0.63  % (16466)Refutation found. Thanks to Tanya!
% 1.82/0.63  % SZS status Theorem for theBenchmark
% 1.82/0.63  % SZS output start Proof for theBenchmark
% 1.82/0.63  fof(f1462,plain,(
% 1.82/0.63    $false),
% 1.82/0.63    inference(avatar_sat_refutation,[],[f181,f191,f264,f266,f416,f541,f547,f589,f643,f651,f660,f846,f1406,f1461])).
% 1.82/0.63  fof(f1461,plain,(
% 1.82/0.63    spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_14 | ~spl7_20 | ~spl7_28 | ~spl7_30),
% 1.82/0.63    inference(avatar_contradiction_clause,[],[f1460])).
% 1.82/0.63  fof(f1460,plain,(
% 1.82/0.63    $false | (spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_14 | ~spl7_20 | ~spl7_28 | ~spl7_30)),
% 1.82/0.63    inference(subsumption_resolution,[],[f1454,f859])).
% 1.82/0.63  fof(f859,plain,(
% 1.82/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_5 | ~spl7_6 | ~spl7_20)),
% 1.82/0.63    inference(forward_demodulation,[],[f858,f263])).
% 1.82/0.63  fof(f263,plain,(
% 1.82/0.63    k1_xboole_0 = sK2 | ~spl7_6),
% 1.82/0.63    inference(avatar_component_clause,[],[f261])).
% 1.82/0.63  fof(f261,plain,(
% 1.82/0.63    spl7_6 <=> k1_xboole_0 = sK2),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.82/0.63  fof(f858,plain,(
% 1.82/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_5 | ~spl7_20)),
% 1.82/0.63    inference(forward_demodulation,[],[f588,f257])).
% 1.82/0.63  fof(f257,plain,(
% 1.82/0.63    k1_xboole_0 = sK1 | ~spl7_5),
% 1.82/0.63    inference(avatar_component_clause,[],[f255])).
% 1.82/0.63  fof(f255,plain,(
% 1.82/0.63    spl7_5 <=> k1_xboole_0 = sK1),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.82/0.63  fof(f588,plain,(
% 1.82/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl7_20),
% 1.82/0.63    inference(avatar_component_clause,[],[f586])).
% 1.82/0.63  fof(f586,plain,(
% 1.82/0.63    spl7_20 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.82/0.63  fof(f1454,plain,(
% 1.82/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_14 | ~spl7_28 | ~spl7_30)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f661,f659,f1412,f848,f161])).
% 1.82/0.63  fof(f161,plain,(
% 1.82/0.63    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 1.82/0.63    inference(equality_resolution,[],[f149])).
% 1.82/0.63  fof(f149,plain,(
% 1.82/0.63    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f80])).
% 2.02/0.63  fof(f80,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.02/0.63    inference(flattening,[],[f79])).
% 2.02/0.63  fof(f79,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.02/0.63    inference(ennf_transformation,[],[f36])).
% 2.02/0.63  fof(f36,axiom,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 2.02/0.63  fof(f848,plain,(
% 2.02/0.63    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_5 | ~spl7_6 | ~spl7_28)),
% 2.02/0.63    inference(forward_demodulation,[],[f847,f263])).
% 2.02/0.63  fof(f847,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_5 | ~spl7_28)),
% 2.02/0.63    inference(forward_demodulation,[],[f642,f257])).
% 2.02/0.63  fof(f642,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl7_28),
% 2.02/0.63    inference(avatar_component_clause,[],[f640])).
% 2.02/0.63  fof(f640,plain,(
% 2.02/0.63    spl7_28 <=> v1_funct_2(sK2,k1_xboole_0,sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.02/0.63  fof(f1412,plain,(
% 2.02/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_14)),
% 2.02/0.63    inference(forward_demodulation,[],[f1411,f887])).
% 2.02/0.63  fof(f887,plain,(
% 2.02/0.63    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl7_5 | ~spl7_6 | ~spl7_14)),
% 2.02/0.63    inference(backward_demodulation,[],[f672,f885])).
% 2.02/0.63  fof(f885,plain,(
% 2.02/0.63    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl7_5 | ~spl7_6 | ~spl7_14)),
% 2.02/0.63    inference(forward_demodulation,[],[f884,f152])).
% 2.02/0.63  fof(f152,plain,(
% 2.02/0.63    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.02/0.63    inference(definition_unfolding,[],[f97,f99])).
% 2.02/0.63  fof(f99,plain,(
% 2.02/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f34])).
% 2.02/0.63  fof(f34,axiom,(
% 2.02/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.02/0.63  fof(f97,plain,(
% 2.02/0.63    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f19,axiom,(
% 2.02/0.63    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 2.02/0.63  fof(f884,plain,(
% 2.02/0.63    k6_partfun1(k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl7_5 | ~spl7_6 | ~spl7_14)),
% 2.02/0.63    inference(forward_demodulation,[],[f883,f263])).
% 2.02/0.63  fof(f883,plain,(
% 2.02/0.63    k6_partfun1(k1_xboole_0) = k4_relat_1(sK2) | (~spl7_5 | ~spl7_14)),
% 2.02/0.63    inference(forward_demodulation,[],[f415,f257])).
% 2.02/0.63  fof(f415,plain,(
% 2.02/0.63    k4_relat_1(sK2) = k6_partfun1(sK1) | ~spl7_14),
% 2.02/0.63    inference(avatar_component_clause,[],[f413])).
% 2.02/0.63  fof(f413,plain,(
% 2.02/0.63    spl7_14 <=> k4_relat_1(sK2) = k6_partfun1(sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.02/0.63  fof(f672,plain,(
% 2.02/0.63    k4_relat_1(k1_xboole_0) = k2_funct_1(k1_xboole_0) | ~spl7_6),
% 2.02/0.63    inference(backward_demodulation,[],[f219,f263])).
% 2.02/0.63  fof(f219,plain,(
% 2.02/0.63    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f93,f90,f188,f125])).
% 2.02/0.63  fof(f125,plain,(
% 2.02/0.63    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f59])).
% 2.02/0.63  fof(f59,plain,(
% 2.02/0.63    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f58])).
% 2.02/0.63  fof(f58,plain,(
% 2.02/0.63    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f21])).
% 2.02/0.63  fof(f21,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 2.02/0.63  fof(f188,plain,(
% 2.02/0.63    v1_relat_1(sK2)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f92,f140])).
% 2.02/0.63  fof(f140,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f73])).
% 2.02/0.63  fof(f73,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f29])).
% 2.02/0.63  fof(f29,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.02/0.63  fof(f92,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.63    inference(cnf_transformation,[],[f82])).
% 2.02/0.63  fof(f82,plain,(
% 2.02/0.63    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f81])).
% 2.02/0.63  fof(f81,plain,(
% 2.02/0.63    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f41,plain,(
% 2.02/0.63    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.02/0.63    inference(flattening,[],[f40])).
% 2.02/0.63  fof(f40,plain,(
% 2.02/0.63    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.02/0.63    inference(ennf_transformation,[],[f38])).
% 2.02/0.63  fof(f38,negated_conjecture,(
% 2.02/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.02/0.63    inference(negated_conjecture,[],[f37])).
% 2.02/0.63  fof(f37,conjecture,(
% 2.02/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 2.02/0.63  fof(f90,plain,(
% 2.02/0.63    v1_funct_1(sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f82])).
% 2.02/0.63  fof(f93,plain,(
% 2.02/0.63    v2_funct_1(sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f82])).
% 2.02/0.63  fof(f1411,plain,(
% 2.02/0.63    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl7_2 | ~spl7_5 | ~spl7_6)),
% 2.02/0.63    inference(forward_demodulation,[],[f1410,f263])).
% 2.02/0.63  fof(f1410,plain,(
% 2.02/0.63    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl7_2 | ~spl7_5)),
% 2.02/0.63    inference(forward_demodulation,[],[f176,f257])).
% 2.02/0.63  fof(f176,plain,(
% 2.02/0.63    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl7_2),
% 2.02/0.63    inference(avatar_component_clause,[],[f174])).
% 2.02/0.63  fof(f174,plain,(
% 2.02/0.63    spl7_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.02/0.63  fof(f659,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK0) | ~spl7_30),
% 2.02/0.63    inference(avatar_component_clause,[],[f657])).
% 2.02/0.63  fof(f657,plain,(
% 2.02/0.63    spl7_30 <=> r1_tarski(k1_xboole_0,sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 2.02/0.63  fof(f661,plain,(
% 2.02/0.63    v1_funct_1(k1_xboole_0) | ~spl7_6),
% 2.02/0.63    inference(backward_demodulation,[],[f90,f263])).
% 2.02/0.63  fof(f1406,plain,(
% 2.02/0.63    spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_14 | ~spl7_29),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f1405])).
% 2.02/0.63  fof(f1405,plain,(
% 2.02/0.63    $false | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_14 | ~spl7_29)),
% 2.02/0.63    inference(subsumption_resolution,[],[f1397,f1293])).
% 2.02/0.63  fof(f1293,plain,(
% 2.02/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_14)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f96,f1286,f163])).
% 2.02/0.63  fof(f163,plain,(
% 2.02/0.63    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP4(X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f163_D])).
% 2.02/0.63  fof(f163_D,plain,(
% 2.02/0.63    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP4(X1)) )),
% 2.02/0.63    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 2.02/0.63  fof(f1286,plain,(
% 2.02/0.63    ~sP4(k1_xboole_0) | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_14)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f1122,f164])).
% 2.02/0.63  fof(f164,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP4(X1)) )),
% 2.02/0.63    inference(general_splitting,[],[f145,f163_D])).
% 2.02/0.63  fof(f145,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f78])).
% 2.02/0.63  fof(f78,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f7])).
% 2.02/0.63  fof(f7,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 2.02/0.63  fof(f1122,plain,(
% 2.02/0.63    r2_hidden(sK3(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)),k1_xboole_0) | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_14)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f974,f136])).
% 2.02/0.63  fof(f136,plain,(
% 2.02/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f88])).
% 2.02/0.63  fof(f88,plain,(
% 2.02/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f86,f87])).
% 2.02/0.63  fof(f87,plain,(
% 2.02/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f86,plain,(
% 2.02/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.63    inference(rectify,[],[f85])).
% 2.02/0.63  fof(f85,plain,(
% 2.02/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.63    inference(nnf_transformation,[],[f72])).
% 2.02/0.63  fof(f72,plain,(
% 2.02/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f1])).
% 2.02/0.63  fof(f1,axiom,(
% 2.02/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.02/0.63  fof(f974,plain,(
% 2.02/0.63    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_14)),
% 2.02/0.63    inference(forward_demodulation,[],[f812,f885])).
% 2.02/0.63  fof(f812,plain,(
% 2.02/0.63    ~r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) | (spl7_3 | ~spl7_5 | ~spl7_6)),
% 2.02/0.63    inference(backward_demodulation,[],[f750,f257])).
% 2.02/0.63  fof(f750,plain,(
% 2.02/0.63    ~r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(sK1,sK0)) | (spl7_3 | ~spl7_6)),
% 2.02/0.63    inference(backward_demodulation,[],[f545,f263])).
% 2.02/0.63  fof(f545,plain,(
% 2.02/0.63    ~r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(sK1,sK0)) | spl7_3),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f542,f139])).
% 2.02/0.63  fof(f139,plain,(
% 2.02/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f89])).
% 2.02/0.63  fof(f89,plain,(
% 2.02/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.02/0.63    inference(nnf_transformation,[],[f6])).
% 2.02/0.63  fof(f6,axiom,(
% 2.02/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.02/0.63  fof(f542,plain,(
% 2.02/0.63    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_3),
% 2.02/0.63    inference(forward_demodulation,[],[f180,f219])).
% 2.02/0.63  fof(f180,plain,(
% 2.02/0.63    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_3),
% 2.02/0.63    inference(avatar_component_clause,[],[f178])).
% 2.02/0.63  fof(f178,plain,(
% 2.02/0.63    spl7_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.02/0.63  fof(f96,plain,(
% 2.02/0.63    v1_xboole_0(k1_xboole_0)),
% 2.02/0.63    inference(cnf_transformation,[],[f2])).
% 2.02/0.63  fof(f2,axiom,(
% 2.02/0.63    v1_xboole_0(k1_xboole_0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.02/0.63  fof(f1397,plain,(
% 2.02/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_6 | ~spl7_29)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f838,f139])).
% 2.02/0.63  fof(f838,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_6 | ~spl7_29)),
% 2.02/0.63    inference(backward_demodulation,[],[f747,f826])).
% 2.02/0.63  fof(f826,plain,(
% 2.02/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl7_6 | ~spl7_29)),
% 2.02/0.63    inference(backward_demodulation,[],[f676,f825])).
% 2.02/0.63  fof(f825,plain,(
% 2.02/0.63    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) | (~spl7_6 | ~spl7_29)),
% 2.02/0.63    inference(forward_demodulation,[],[f647,f263])).
% 2.02/0.63  fof(f647,plain,(
% 2.02/0.63    k1_xboole_0 = k2_relat_1(k4_relat_1(sK2)) | ~spl7_29),
% 2.02/0.63    inference(avatar_component_clause,[],[f646])).
% 2.02/0.63  fof(f646,plain,(
% 2.02/0.63    spl7_29 <=> k1_xboole_0 = k2_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 2.02/0.63  fof(f676,plain,(
% 2.02/0.63    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl7_6),
% 2.02/0.63    inference(backward_demodulation,[],[f227,f263])).
% 2.02/0.63  fof(f227,plain,(
% 2.02/0.63    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(backward_demodulation,[],[f221,f219])).
% 2.02/0.63  fof(f221,plain,(
% 2.02/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f93,f90,f188,f127])).
% 2.02/0.63  fof(f127,plain,(
% 2.02/0.63    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f61])).
% 2.02/0.63  fof(f61,plain,(
% 2.02/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f60])).
% 2.02/0.63  fof(f60,plain,(
% 2.02/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f27])).
% 2.02/0.63  fof(f27,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.02/0.63  fof(f747,plain,(
% 2.02/0.63    r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~spl7_6),
% 2.02/0.63    inference(backward_demodulation,[],[f519,f263])).
% 2.02/0.63  fof(f519,plain,(
% 2.02/0.63    r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f188,f450,f132])).
% 2.02/0.63  fof(f132,plain,(
% 2.02/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f84])).
% 2.02/0.63  fof(f84,plain,(
% 2.02/0.63    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.02/0.63    inference(nnf_transformation,[],[f69])).
% 2.02/0.63  fof(f69,plain,(
% 2.02/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f8])).
% 2.02/0.63  fof(f8,axiom,(
% 2.02/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.02/0.63  fof(f450,plain,(
% 2.02/0.63    v4_relat_1(sK2,k1_relat_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f232,f142])).
% 2.02/0.63  fof(f142,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f75])).
% 2.02/0.63  fof(f75,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f39])).
% 2.02/0.63  fof(f39,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.02/0.63    inference(pure_predicate_removal,[],[f30])).
% 2.02/0.63  fof(f30,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.02/0.63  fof(f232,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.02/0.63    inference(forward_demodulation,[],[f216,f192])).
% 2.02/0.63  fof(f192,plain,(
% 2.02/0.63    sK1 = k2_relat_1(sK2)),
% 2.02/0.63    inference(forward_demodulation,[],[f187,f94])).
% 2.02/0.63  fof(f94,plain,(
% 2.02/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f82])).
% 2.02/0.63  fof(f187,plain,(
% 2.02/0.63    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f92,f141])).
% 2.02/0.63  fof(f141,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f74])).
% 2.02/0.63  fof(f74,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f31])).
% 2.02/0.63  fof(f31,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.02/0.63  fof(f216,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f90,f188,f122])).
% 2.02/0.63  fof(f122,plain,(
% 2.02/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f55])).
% 2.02/0.63  fof(f55,plain,(
% 2.02/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f54])).
% 2.02/0.63  fof(f54,plain,(
% 2.02/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f35])).
% 2.02/0.63  fof(f35,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 2.02/0.63  fof(f846,plain,(
% 2.02/0.63    ~spl7_6 | spl7_13 | ~spl7_29),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f845])).
% 2.02/0.63  fof(f845,plain,(
% 2.02/0.63    $false | (~spl7_6 | spl7_13 | ~spl7_29)),
% 2.02/0.63    inference(subsumption_resolution,[],[f834,f152])).
% 2.02/0.63  fof(f834,plain,(
% 2.02/0.63    k1_xboole_0 != k6_partfun1(k1_xboole_0) | (~spl7_6 | spl7_13 | ~spl7_29)),
% 2.02/0.63    inference(backward_demodulation,[],[f708,f826])).
% 2.02/0.63  fof(f708,plain,(
% 2.02/0.63    k1_xboole_0 != k6_partfun1(k1_relat_1(k1_xboole_0)) | (~spl7_6 | spl7_13)),
% 2.02/0.63    inference(backward_demodulation,[],[f411,f263])).
% 2.02/0.63  fof(f411,plain,(
% 2.02/0.63    sK2 != k6_partfun1(k1_relat_1(sK2)) | spl7_13),
% 2.02/0.63    inference(avatar_component_clause,[],[f409])).
% 2.02/0.63  fof(f409,plain,(
% 2.02/0.63    spl7_13 <=> sK2 = k6_partfun1(k1_relat_1(sK2))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.02/0.63  fof(f660,plain,(
% 2.02/0.63    spl7_30 | ~spl7_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f319,f255,f657])).
% 2.02/0.63  fof(f319,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | r1_tarski(k1_xboole_0,sK0)),
% 2.02/0.63    inference(forward_demodulation,[],[f318,f192])).
% 2.02/0.63  fof(f318,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != k2_relat_1(sK2)),
% 2.02/0.63    inference(subsumption_resolution,[],[f317,f188])).
% 2.02/0.63  fof(f317,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.63    inference(superposition,[],[f237,f118])).
% 2.02/0.63  fof(f118,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f83])).
% 2.02/0.63  fof(f83,plain,(
% 2.02/0.63    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(nnf_transformation,[],[f51])).
% 2.02/0.63  fof(f51,plain,(
% 2.02/0.63    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f16])).
% 2.02/0.63  fof(f16,axiom,(
% 2.02/0.63    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 2.02/0.63  fof(f237,plain,(
% 2.02/0.63    r1_tarski(k1_relat_1(sK2),sK0)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f188,f186,f132])).
% 2.02/0.63  fof(f186,plain,(
% 2.02/0.63    v4_relat_1(sK2,sK0)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f92,f142])).
% 2.02/0.63  fof(f651,plain,(
% 2.02/0.63    spl7_29 | ~spl7_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f650,f255,f646])).
% 2.02/0.63  fof(f650,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | k1_xboole_0 = k2_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(subsumption_resolution,[],[f348,f231])).
% 2.02/0.63  fof(f231,plain,(
% 2.02/0.63    v1_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(forward_demodulation,[],[f217,f219])).
% 2.02/0.63  fof(f217,plain,(
% 2.02/0.63    v1_relat_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f90,f188,f123])).
% 2.02/0.63  fof(f123,plain,(
% 2.02/0.63    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f57])).
% 2.02/0.63  fof(f57,plain,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f56])).
% 2.02/0.63  fof(f56,plain,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f22])).
% 2.02/0.63  fof(f22,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.02/0.63  fof(f348,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | k1_xboole_0 = k2_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(superposition,[],[f117,f226])).
% 2.02/0.63  fof(f226,plain,(
% 2.02/0.63    sK1 = k1_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(backward_demodulation,[],[f225,f219])).
% 2.02/0.63  fof(f225,plain,(
% 2.02/0.63    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(forward_demodulation,[],[f220,f192])).
% 2.02/0.63  fof(f220,plain,(
% 2.02/0.63    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f93,f90,f188,f126])).
% 2.02/0.63  fof(f126,plain,(
% 2.02/0.63    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f61])).
% 2.02/0.63  fof(f117,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f83])).
% 2.02/0.63  fof(f643,plain,(
% 2.02/0.63    spl7_28 | ~spl7_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f638,f255,f640])).
% 2.02/0.63  fof(f638,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | v1_funct_2(sK2,k1_xboole_0,sK1)),
% 2.02/0.63    inference(forward_demodulation,[],[f637,f192])).
% 2.02/0.63  fof(f637,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_xboole_0,sK1) | k1_xboole_0 != k2_relat_1(sK2)),
% 2.02/0.63    inference(subsumption_resolution,[],[f395,f188])).
% 2.02/0.63  fof(f395,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_xboole_0,sK1) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.63    inference(superposition,[],[f233,f118])).
% 2.02/0.63  fof(f233,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 2.02/0.63    inference(forward_demodulation,[],[f215,f192])).
% 2.02/0.63  fof(f215,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f90,f188,f121])).
% 2.02/0.63  fof(f121,plain,(
% 2.02/0.63    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f55])).
% 2.02/0.63  fof(f589,plain,(
% 2.02/0.63    spl7_20 | ~spl7_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f584,f255,f586])).
% 2.02/0.63  fof(f584,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 2.02/0.63    inference(forward_demodulation,[],[f583,f192])).
% 2.02/0.63  fof(f583,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | k1_xboole_0 != k2_relat_1(sK2)),
% 2.02/0.63    inference(subsumption_resolution,[],[f454,f188])).
% 2.02/0.63  fof(f454,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.63    inference(superposition,[],[f232,f118])).
% 2.02/0.63  fof(f547,plain,(
% 2.02/0.63    ~spl7_1 | spl7_3 | spl7_4),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f546])).
% 2.02/0.63  fof(f546,plain,(
% 2.02/0.63    $false | (~spl7_1 | spl7_3 | spl7_4)),
% 2.02/0.63    inference(subsumption_resolution,[],[f544,f302])).
% 2.02/0.63  fof(f302,plain,(
% 2.02/0.63    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl7_1),
% 2.02/0.63    inference(forward_demodulation,[],[f301,f226])).
% 2.02/0.63  fof(f301,plain,(
% 2.02/0.63    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) | ~spl7_1),
% 2.02/0.63    inference(forward_demodulation,[],[f295,f227])).
% 2.02/0.63  fof(f295,plain,(
% 2.02/0.63    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) | ~spl7_1),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f197,f231,f122])).
% 2.02/0.63  fof(f197,plain,(
% 2.02/0.63    v1_funct_1(k4_relat_1(sK2)) | ~spl7_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f196,f188])).
% 2.02/0.63  fof(f196,plain,(
% 2.02/0.63    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl7_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f195,f90])).
% 2.02/0.63  fof(f195,plain,(
% 2.02/0.63    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f194,f93])).
% 2.02/0.63  fof(f194,plain,(
% 2.02/0.63    v1_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 2.02/0.63    inference(superposition,[],[f171,f125])).
% 2.02/0.63  fof(f171,plain,(
% 2.02/0.63    v1_funct_1(k2_funct_1(sK2)) | ~spl7_1),
% 2.02/0.63    inference(avatar_component_clause,[],[f170])).
% 2.02/0.63  fof(f170,plain,(
% 2.02/0.63    spl7_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.02/0.63  fof(f544,plain,(
% 2.02/0.63    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl7_1 | spl7_3 | spl7_4)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f197,f237,f253,f304,f542,f150])).
% 2.02/0.63  fof(f150,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f80])).
% 2.02/0.63  fof(f304,plain,(
% 2.02/0.63    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) | ~spl7_1),
% 2.02/0.63    inference(forward_demodulation,[],[f303,f226])).
% 2.02/0.63  fof(f303,plain,(
% 2.02/0.63    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~spl7_1),
% 2.02/0.63    inference(forward_demodulation,[],[f294,f227])).
% 2.02/0.63  fof(f294,plain,(
% 2.02/0.63    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) | ~spl7_1),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f197,f231,f121])).
% 2.02/0.63  fof(f253,plain,(
% 2.02/0.63    k1_xboole_0 != k1_relat_1(sK2) | spl7_4),
% 2.02/0.63    inference(avatar_component_clause,[],[f251])).
% 2.02/0.63  fof(f251,plain,(
% 2.02/0.63    spl7_4 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.02/0.63  fof(f541,plain,(
% 2.02/0.63    ~spl7_1 | spl7_2 | spl7_4),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f540])).
% 2.02/0.63  fof(f540,plain,(
% 2.02/0.63    $false | (~spl7_1 | spl7_2 | spl7_4)),
% 2.02/0.63    inference(subsumption_resolution,[],[f538,f302])).
% 2.02/0.63  fof(f538,plain,(
% 2.02/0.63    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl7_1 | spl7_2 | spl7_4)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f197,f237,f206,f253,f304,f148])).
% 2.02/0.63  fof(f148,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f80])).
% 2.02/0.63  fof(f206,plain,(
% 2.02/0.63    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | spl7_2),
% 2.02/0.63    inference(subsumption_resolution,[],[f205,f188])).
% 2.02/0.63  fof(f205,plain,(
% 2.02/0.63    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_relat_1(sK2) | spl7_2),
% 2.02/0.63    inference(subsumption_resolution,[],[f204,f90])).
% 2.02/0.63  fof(f204,plain,(
% 2.02/0.63    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_2),
% 2.02/0.63    inference(subsumption_resolution,[],[f199,f93])).
% 2.02/0.63  fof(f199,plain,(
% 2.02/0.63    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_2),
% 2.02/0.63    inference(superposition,[],[f176,f125])).
% 2.02/0.63  fof(f416,plain,(
% 2.02/0.63    ~spl7_13 | spl7_14),
% 2.02/0.63    inference(avatar_split_clause,[],[f407,f413,f409])).
% 2.02/0.63  fof(f407,plain,(
% 2.02/0.63    k4_relat_1(sK2) = k6_partfun1(sK1) | sK2 != k6_partfun1(k1_relat_1(sK2))),
% 2.02/0.63    inference(subsumption_resolution,[],[f406,f192])).
% 2.02/0.63  fof(f406,plain,(
% 2.02/0.63    sK1 != k2_relat_1(sK2) | k4_relat_1(sK2) = k6_partfun1(sK1) | sK2 != k6_partfun1(k1_relat_1(sK2))),
% 2.02/0.63    inference(forward_demodulation,[],[f405,f156])).
% 2.02/0.63  fof(f156,plain,(
% 2.02/0.63    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.02/0.63    inference(definition_unfolding,[],[f105,f99])).
% 2.02/0.63  fof(f105,plain,(
% 2.02/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.02/0.63    inference(cnf_transformation,[],[f17])).
% 2.02/0.63  fof(f17,axiom,(
% 2.02/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.02/0.64  fof(f405,plain,(
% 2.02/0.64    k4_relat_1(sK2) = k6_partfun1(sK1) | sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))),
% 2.02/0.64    inference(forward_demodulation,[],[f404,f219])).
% 2.02/0.64  fof(f404,plain,(
% 2.02/0.64    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))),
% 2.02/0.64    inference(subsumption_resolution,[],[f403,f188])).
% 2.02/0.64  fof(f403,plain,(
% 2.02/0.64    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(sK2)),
% 2.02/0.64    inference(subsumption_resolution,[],[f402,f90])).
% 2.02/0.64  fof(f402,plain,(
% 2.02/0.64    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.64    inference(subsumption_resolution,[],[f401,f154])).
% 2.02/0.64  fof(f154,plain,(
% 2.02/0.64    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.02/0.64    inference(definition_unfolding,[],[f101,f99])).
% 2.02/0.64  fof(f101,plain,(
% 2.02/0.64    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f23])).
% 2.02/0.64  fof(f23,axiom,(
% 2.02/0.64    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.02/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.02/0.64  fof(f401,plain,(
% 2.02/0.64    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.64    inference(subsumption_resolution,[],[f400,f153])).
% 2.02/0.64  fof(f153,plain,(
% 2.02/0.64    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 2.02/0.64    inference(definition_unfolding,[],[f102,f99])).
% 2.02/0.64  fof(f102,plain,(
% 2.02/0.64    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f23])).
% 2.02/0.64  fof(f400,plain,(
% 2.02/0.64    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(k6_partfun1(sK1)) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.64    inference(subsumption_resolution,[],[f398,f93])).
% 2.02/0.64  fof(f398,plain,(
% 2.02/0.64    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(k6_partfun1(sK1)) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.64    inference(superposition,[],[f159,f224])).
% 2.02/0.64  fof(f224,plain,(
% 2.02/0.64    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 2.02/0.64    inference(forward_demodulation,[],[f223,f192])).
% 2.02/0.64  fof(f223,plain,(
% 2.02/0.64    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f188,f157])).
% 2.02/0.64  fof(f157,plain,(
% 2.02/0.64    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(definition_unfolding,[],[f112,f99])).
% 2.02/0.64  fof(f112,plain,(
% 2.02/0.64    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f47])).
% 2.02/0.64  fof(f47,plain,(
% 2.02/0.64    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.02/0.64    inference(ennf_transformation,[],[f18])).
% 2.02/0.64  fof(f18,axiom,(
% 2.02/0.64    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.02/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.02/0.64  fof(f159,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(definition_unfolding,[],[f130,f99])).
% 2.02/0.64  fof(f130,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f67])).
% 2.02/0.64  fof(f67,plain,(
% 2.02/0.64    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(flattening,[],[f66])).
% 2.02/0.64  fof(f66,plain,(
% 2.02/0.64    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.64    inference(ennf_transformation,[],[f28])).
% 2.02/0.64  fof(f28,axiom,(
% 2.02/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.02/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 2.02/0.64  fof(f266,plain,(
% 2.02/0.64    ~spl7_4 | spl7_5),
% 2.02/0.64    inference(avatar_split_clause,[],[f265,f255,f251])).
% 2.02/0.64  fof(f265,plain,(
% 2.02/0.64    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2)),
% 2.02/0.64    inference(subsumption_resolution,[],[f241,f188])).
% 2.02/0.64  fof(f241,plain,(
% 2.02/0.64    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.64    inference(superposition,[],[f117,f192])).
% 2.02/0.64  fof(f264,plain,(
% 2.02/0.64    spl7_6 | ~spl7_5),
% 2.02/0.64    inference(avatar_split_clause,[],[f259,f255,f261])).
% 2.02/0.64  fof(f259,plain,(
% 2.02/0.64    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 2.02/0.64    inference(subsumption_resolution,[],[f240,f188])).
% 2.02/0.64  fof(f240,plain,(
% 2.02/0.64    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 2.02/0.64    inference(superposition,[],[f116,f192])).
% 2.02/0.64  fof(f116,plain,(
% 2.02/0.64    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f50])).
% 2.02/0.64  fof(f50,plain,(
% 2.02/0.64    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(flattening,[],[f49])).
% 2.02/0.64  fof(f49,plain,(
% 2.02/0.64    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(ennf_transformation,[],[f15])).
% 2.02/0.64  fof(f15,axiom,(
% 2.02/0.64    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.02/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.02/0.64  fof(f191,plain,(
% 2.02/0.64    spl7_1),
% 2.02/0.64    inference(avatar_contradiction_clause,[],[f190])).
% 2.02/0.64  fof(f190,plain,(
% 2.02/0.64    $false | spl7_1),
% 2.02/0.64    inference(subsumption_resolution,[],[f188,f182])).
% 2.02/0.64  fof(f182,plain,(
% 2.02/0.64    ~v1_relat_1(sK2) | spl7_1),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f90,f172,f124])).
% 2.02/0.64  fof(f124,plain,(
% 2.02/0.64    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f57])).
% 2.02/0.64  fof(f172,plain,(
% 2.02/0.64    ~v1_funct_1(k2_funct_1(sK2)) | spl7_1),
% 2.02/0.64    inference(avatar_component_clause,[],[f170])).
% 2.02/0.64  fof(f181,plain,(
% 2.02/0.64    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 2.02/0.64    inference(avatar_split_clause,[],[f95,f178,f174,f170])).
% 2.02/0.64  fof(f95,plain,(
% 2.02/0.64    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.02/0.64    inference(cnf_transformation,[],[f82])).
% 2.02/0.64  % SZS output end Proof for theBenchmark
% 2.02/0.64  % (16466)------------------------------
% 2.02/0.64  % (16466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.64  % (16466)Termination reason: Refutation
% 2.02/0.64  
% 2.02/0.64  % (16466)Memory used [KB]: 11385
% 2.02/0.64  % (16466)Time elapsed: 0.220 s
% 2.02/0.64  % (16466)------------------------------
% 2.02/0.64  % (16466)------------------------------
% 2.02/0.64  % (16431)Success in time 0.277 s
%------------------------------------------------------------------------------
