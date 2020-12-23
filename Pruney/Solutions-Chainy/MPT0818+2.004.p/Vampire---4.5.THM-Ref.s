%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:16 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 132 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  236 ( 360 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f87,f101,f415,f419,f462,f475,f532,f544])).

fof(f544,plain,
    ( ~ spl4_1
    | spl4_3
    | ~ spl4_43
    | ~ spl4_52 ),
    inference(avatar_contradiction_clause,[],[f535])).

fof(f535,plain,
    ( $false
    | ~ spl4_1
    | spl4_3
    | ~ spl4_43
    | ~ spl4_52 ),
    inference(unit_resulting_resolution,[],[f54,f461,f64,f531,f190])).

fof(f190,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_tarski(X5,k2_zfmisc_1(X8,X9))
      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ r1_tarski(X9,X7)
      | ~ r1_tarski(X8,X6) ) ),
    inference(resolution,[],[f117,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f117,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f531,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl4_52
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f64,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f461,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl4_43
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f54,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_1
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f532,plain,
    ( spl4_52
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f523,f473,f529])).

fof(f473,plain,
    ( spl4_44
  <=> ! [X0] :
        ( r1_tarski(k1_relat_1(sK3),X0)
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f523,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_44 ),
    inference(resolution,[],[f474,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f474,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r1_tarski(k1_relat_1(sK3),X0) )
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f473])).

fof(f475,plain,
    ( spl4_44
    | ~ spl4_7
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f455,f417,f98,f473])).

fof(f98,plain,
    ( spl4_7
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f417,plain,
    ( spl4_40
  <=> ! [X5,X4] :
        ( r1_tarski(k1_relat_1(sK3),X4)
        | ~ v4_relat_1(sK3,X5)
        | ~ r1_tarski(X5,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f455,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(sK3),X0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_7
    | ~ spl4_40 ),
    inference(resolution,[],[f418,f100])).

fof(f100,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f418,plain,
    ( ! [X4,X5] :
        ( ~ v4_relat_1(sK3,X5)
        | r1_tarski(k1_relat_1(sK3),X4)
        | ~ r1_tarski(X5,X4) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f417])).

fof(f462,plain,
    ( spl4_43
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f444,f413,f459])).

fof(f413,plain,
    ( spl4_39
  <=> ! [X3] :
        ( r1_tarski(sK3,X3)
        | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f444,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_39 ),
    inference(resolution,[],[f414,f49])).

fof(f414,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),X3)
        | r1_tarski(sK3,X3) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f413])).

fof(f419,plain,
    ( spl4_40
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f179,f84,f417])).

fof(f84,plain,
    ( spl4_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f179,plain,
    ( ! [X4,X5] :
        ( r1_tarski(k1_relat_1(sK3),X4)
        | ~ v4_relat_1(sK3,X5)
        | ~ r1_tarski(X5,X4) )
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f86])).

fof(f86,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f106,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X6)
      | r1_tarski(k1_relat_1(X6),X5)
      | ~ v4_relat_1(X6,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f415,plain,
    ( spl4_39
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f168,f84,f413])).

fof(f168,plain,
    ( ! [X3] :
        ( r1_tarski(sK3,X3)
        | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),X3) )
    | ~ spl4_6 ),
    inference(resolution,[],[f105,f86])).

fof(f105,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(X2,X3)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X3) ) ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f101,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f95,f57,f98])).

fof(f57,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f95,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f44,f59])).

fof(f59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f87,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f80,f57,f84])).

fof(f80,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f74,f59])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f65,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & r1_tarski(k2_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & r1_tarski(k2_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & r1_tarski(k2_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_tarski(k2_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f60,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f32,f52])).

fof(f32,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:47:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (22233)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (22248)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (22223)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (22239)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (22221)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.55  % (22247)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.56  % (22232)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (22237)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.56  % (22226)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.57  % (22246)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.57  % (22238)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.57  % (22224)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.57  % (22235)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (22222)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (22245)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.58  % (22227)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.58  % (22229)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.58  % (22242)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.58  % (22231)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.59  % (22241)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.59  % (22244)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.71/0.60  % (22223)Refutation found. Thanks to Tanya!
% 1.71/0.60  % SZS status Theorem for theBenchmark
% 1.71/0.60  % SZS output start Proof for theBenchmark
% 1.71/0.60  fof(f545,plain,(
% 1.71/0.60    $false),
% 1.71/0.60    inference(avatar_sat_refutation,[],[f55,f60,f65,f87,f101,f415,f419,f462,f475,f532,f544])).
% 1.71/0.60  fof(f544,plain,(
% 1.71/0.60    ~spl4_1 | spl4_3 | ~spl4_43 | ~spl4_52),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f535])).
% 1.71/0.60  fof(f535,plain,(
% 1.71/0.60    $false | (~spl4_1 | spl4_3 | ~spl4_43 | ~spl4_52)),
% 1.71/0.60    inference(unit_resulting_resolution,[],[f54,f461,f64,f531,f190])).
% 1.71/0.60  fof(f190,plain,(
% 1.71/0.60    ( ! [X6,X8,X7,X5,X9] : (~r1_tarski(X5,k2_zfmisc_1(X8,X9)) | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~r1_tarski(X9,X7) | ~r1_tarski(X8,X6)) )),
% 1.71/0.60    inference(resolution,[],[f117,f48])).
% 1.71/0.60  fof(f48,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f24])).
% 1.71/0.60  fof(f24,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.71/0.60    inference(flattening,[],[f23])).
% 1.71/0.60  fof(f23,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.71/0.60    inference(ennf_transformation,[],[f3])).
% 1.71/0.60  fof(f3,axiom,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 1.71/0.60  fof(f117,plain,(
% 1.71/0.60    ( ! [X4,X2,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X3,X4)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~r1_tarski(X1,X2)) )),
% 1.71/0.60    inference(resolution,[],[f47,f43])).
% 1.71/0.60  fof(f43,plain,(
% 1.71/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f30])).
% 1.71/0.60  fof(f30,plain,(
% 1.71/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.71/0.60    inference(nnf_transformation,[],[f4])).
% 1.71/0.60  fof(f4,axiom,(
% 1.71/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.60  fof(f47,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f22])).
% 1.71/0.60  fof(f22,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.71/0.60    inference(flattening,[],[f21])).
% 1.71/0.60  fof(f21,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.71/0.60    inference(ennf_transformation,[],[f10])).
% 1.71/0.60  fof(f10,axiom,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).
% 1.71/0.60  fof(f531,plain,(
% 1.71/0.60    r1_tarski(k1_relat_1(sK3),sK2) | ~spl4_52),
% 1.71/0.60    inference(avatar_component_clause,[],[f529])).
% 1.71/0.60  fof(f529,plain,(
% 1.71/0.60    spl4_52 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.71/0.60  fof(f64,plain,(
% 1.71/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.71/0.60    inference(avatar_component_clause,[],[f62])).
% 1.71/0.60  fof(f62,plain,(
% 1.71/0.60    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.71/0.60  fof(f461,plain,(
% 1.71/0.60    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_43),
% 1.71/0.60    inference(avatar_component_clause,[],[f459])).
% 1.71/0.60  fof(f459,plain,(
% 1.71/0.60    spl4_43 <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.71/0.60  fof(f54,plain,(
% 1.71/0.60    r1_tarski(k2_relat_1(sK3),sK1) | ~spl4_1),
% 1.71/0.60    inference(avatar_component_clause,[],[f52])).
% 1.71/0.60  fof(f52,plain,(
% 1.71/0.60    spl4_1 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.71/0.60  fof(f532,plain,(
% 1.71/0.60    spl4_52 | ~spl4_44),
% 1.71/0.60    inference(avatar_split_clause,[],[f523,f473,f529])).
% 1.71/0.60  fof(f473,plain,(
% 1.71/0.60    spl4_44 <=> ! [X0] : (r1_tarski(k1_relat_1(sK3),X0) | ~r1_tarski(sK2,X0))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.71/0.60  fof(f523,plain,(
% 1.71/0.60    r1_tarski(k1_relat_1(sK3),sK2) | ~spl4_44),
% 1.71/0.60    inference(resolution,[],[f474,f49])).
% 1.71/0.60  fof(f49,plain,(
% 1.71/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.71/0.60    inference(equality_resolution,[],[f40])).
% 1.71/0.60  fof(f40,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.71/0.60    inference(cnf_transformation,[],[f29])).
% 1.71/0.60  fof(f29,plain,(
% 1.71/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.60    inference(flattening,[],[f28])).
% 1.71/0.60  fof(f28,plain,(
% 1.71/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.60    inference(nnf_transformation,[],[f1])).
% 1.71/0.60  fof(f1,axiom,(
% 1.71/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.60  fof(f474,plain,(
% 1.71/0.60    ( ! [X0] : (~r1_tarski(sK2,X0) | r1_tarski(k1_relat_1(sK3),X0)) ) | ~spl4_44),
% 1.71/0.60    inference(avatar_component_clause,[],[f473])).
% 1.71/0.60  fof(f475,plain,(
% 1.71/0.60    spl4_44 | ~spl4_7 | ~spl4_40),
% 1.71/0.60    inference(avatar_split_clause,[],[f455,f417,f98,f473])).
% 1.71/0.60  fof(f98,plain,(
% 1.71/0.60    spl4_7 <=> v4_relat_1(sK3,sK2)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.71/0.60  fof(f417,plain,(
% 1.71/0.60    spl4_40 <=> ! [X5,X4] : (r1_tarski(k1_relat_1(sK3),X4) | ~v4_relat_1(sK3,X5) | ~r1_tarski(X5,X4))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.71/0.60  fof(f455,plain,(
% 1.71/0.60    ( ! [X0] : (r1_tarski(k1_relat_1(sK3),X0) | ~r1_tarski(sK2,X0)) ) | (~spl4_7 | ~spl4_40)),
% 1.71/0.60    inference(resolution,[],[f418,f100])).
% 1.71/0.60  fof(f100,plain,(
% 1.71/0.60    v4_relat_1(sK3,sK2) | ~spl4_7),
% 1.71/0.60    inference(avatar_component_clause,[],[f98])).
% 1.71/0.60  fof(f418,plain,(
% 1.71/0.60    ( ! [X4,X5] : (~v4_relat_1(sK3,X5) | r1_tarski(k1_relat_1(sK3),X4) | ~r1_tarski(X5,X4)) ) | ~spl4_40),
% 1.71/0.60    inference(avatar_component_clause,[],[f417])).
% 1.71/0.60  fof(f462,plain,(
% 1.71/0.60    spl4_43 | ~spl4_39),
% 1.71/0.60    inference(avatar_split_clause,[],[f444,f413,f459])).
% 1.71/0.60  fof(f413,plain,(
% 1.71/0.60    spl4_39 <=> ! [X3] : (r1_tarski(sK3,X3) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),X3))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.71/0.60  fof(f444,plain,(
% 1.71/0.60    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_39),
% 1.71/0.60    inference(resolution,[],[f414,f49])).
% 1.71/0.60  fof(f414,plain,(
% 1.71/0.60    ( ! [X3] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),X3) | r1_tarski(sK3,X3)) ) | ~spl4_39),
% 1.71/0.60    inference(avatar_component_clause,[],[f413])).
% 1.71/0.60  fof(f419,plain,(
% 1.71/0.60    spl4_40 | ~spl4_6),
% 1.71/0.60    inference(avatar_split_clause,[],[f179,f84,f417])).
% 1.71/0.60  fof(f84,plain,(
% 1.71/0.60    spl4_6 <=> v1_relat_1(sK3)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.71/0.60  fof(f179,plain,(
% 1.71/0.60    ( ! [X4,X5] : (r1_tarski(k1_relat_1(sK3),X4) | ~v4_relat_1(sK3,X5) | ~r1_tarski(X5,X4)) ) | ~spl4_6),
% 1.71/0.60    inference(resolution,[],[f106,f86])).
% 1.71/0.60  fof(f86,plain,(
% 1.71/0.60    v1_relat_1(sK3) | ~spl4_6),
% 1.71/0.60    inference(avatar_component_clause,[],[f84])).
% 1.71/0.60  fof(f106,plain,(
% 1.71/0.60    ( ! [X6,X4,X5] : (~v1_relat_1(X6) | r1_tarski(k1_relat_1(X6),X5) | ~v4_relat_1(X6,X4) | ~r1_tarski(X4,X5)) )),
% 1.71/0.60    inference(resolution,[],[f46,f37])).
% 1.71/0.60  fof(f37,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f27])).
% 1.71/0.60  fof(f27,plain,(
% 1.71/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(nnf_transformation,[],[f17])).
% 1.71/0.60  fof(f17,plain,(
% 1.71/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(ennf_transformation,[],[f6])).
% 1.71/0.60  fof(f6,axiom,(
% 1.71/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.71/0.60  fof(f46,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f20])).
% 1.71/0.60  fof(f20,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.71/0.60    inference(flattening,[],[f19])).
% 1.71/0.60  fof(f19,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.71/0.60    inference(ennf_transformation,[],[f2])).
% 1.71/0.60  fof(f2,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.71/0.60  fof(f415,plain,(
% 1.71/0.60    spl4_39 | ~spl4_6),
% 1.71/0.60    inference(avatar_split_clause,[],[f168,f84,f413])).
% 1.71/0.60  fof(f168,plain,(
% 1.71/0.60    ( ! [X3] : (r1_tarski(sK3,X3) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),X3)) ) | ~spl4_6),
% 1.71/0.60    inference(resolution,[],[f105,f86])).
% 1.71/0.60  fof(f105,plain,(
% 1.71/0.60    ( ! [X2,X3] : (~v1_relat_1(X2) | r1_tarski(X2,X3) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X3)) )),
% 1.71/0.60    inference(resolution,[],[f46,f34])).
% 1.71/0.60  fof(f34,plain,(
% 1.71/0.60    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f15])).
% 1.71/0.60  fof(f15,plain,(
% 1.71/0.60    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.60    inference(ennf_transformation,[],[f8])).
% 1.71/0.60  fof(f8,axiom,(
% 1.71/0.60    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.71/0.60  fof(f101,plain,(
% 1.71/0.60    spl4_7 | ~spl4_2),
% 1.71/0.60    inference(avatar_split_clause,[],[f95,f57,f98])).
% 1.71/0.60  fof(f57,plain,(
% 1.71/0.60    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.60  fof(f95,plain,(
% 1.71/0.60    v4_relat_1(sK3,sK2) | ~spl4_2),
% 1.71/0.60    inference(resolution,[],[f44,f59])).
% 1.71/0.60  fof(f59,plain,(
% 1.71/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_2),
% 1.71/0.60    inference(avatar_component_clause,[],[f57])).
% 1.71/0.60  fof(f44,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f18])).
% 1.71/0.60  fof(f18,plain,(
% 1.71/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.60    inference(ennf_transformation,[],[f9])).
% 1.71/0.60  fof(f9,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.60  fof(f87,plain,(
% 1.71/0.60    spl4_6 | ~spl4_2),
% 1.71/0.60    inference(avatar_split_clause,[],[f80,f57,f84])).
% 1.71/0.60  fof(f80,plain,(
% 1.71/0.60    v1_relat_1(sK3) | ~spl4_2),
% 1.71/0.60    inference(resolution,[],[f74,f59])).
% 1.71/0.60  fof(f74,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.71/0.60    inference(resolution,[],[f35,f36])).
% 1.71/0.60  fof(f36,plain,(
% 1.71/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f7])).
% 1.71/0.60  fof(f7,axiom,(
% 1.71/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.71/0.60  fof(f35,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f16])).
% 1.71/0.60  fof(f16,plain,(
% 1.71/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.60    inference(ennf_transformation,[],[f5])).
% 1.71/0.60  fof(f5,axiom,(
% 1.71/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.71/0.60  fof(f65,plain,(
% 1.71/0.60    ~spl4_3),
% 1.71/0.60    inference(avatar_split_clause,[],[f33,f62])).
% 1.71/0.60  fof(f33,plain,(
% 1.71/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.71/0.60    inference(cnf_transformation,[],[f26])).
% 1.71/0.60  fof(f26,plain,(
% 1.71/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & r1_tarski(k2_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.71/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).
% 1.71/0.60  fof(f25,plain,(
% 1.71/0.60    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & r1_tarski(k2_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 1.71/0.60    introduced(choice_axiom,[])).
% 1.71/0.60  fof(f14,plain,(
% 1.71/0.60    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.71/0.60    inference(flattening,[],[f13])).
% 1.71/0.60  fof(f13,plain,(
% 1.71/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.71/0.60    inference(ennf_transformation,[],[f12])).
% 1.71/0.60  fof(f12,negated_conjecture,(
% 1.71/0.60    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 1.71/0.60    inference(negated_conjecture,[],[f11])).
% 1.71/0.60  fof(f11,conjecture,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 1.71/0.60  fof(f60,plain,(
% 1.71/0.60    spl4_2),
% 1.71/0.60    inference(avatar_split_clause,[],[f31,f57])).
% 1.71/0.60  fof(f31,plain,(
% 1.71/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.71/0.60    inference(cnf_transformation,[],[f26])).
% 1.71/0.60  fof(f55,plain,(
% 1.71/0.60    spl4_1),
% 1.71/0.60    inference(avatar_split_clause,[],[f32,f52])).
% 1.71/0.60  fof(f32,plain,(
% 1.71/0.60    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.71/0.60    inference(cnf_transformation,[],[f26])).
% 1.71/0.60  % SZS output end Proof for theBenchmark
% 1.71/0.60  % (22223)------------------------------
% 1.71/0.60  % (22223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (22223)Termination reason: Refutation
% 1.71/0.60  
% 1.71/0.60  % (22223)Memory used [KB]: 6524
% 1.71/0.60  % (22223)Time elapsed: 0.189 s
% 1.71/0.60  % (22223)------------------------------
% 1.71/0.60  % (22223)------------------------------
% 1.71/0.60  % (22218)Success in time 0.229 s
%------------------------------------------------------------------------------
