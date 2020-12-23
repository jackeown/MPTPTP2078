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
% DateTime   : Thu Dec  3 13:06:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 255 expanded)
%              Number of leaves         :   36 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  454 ( 693 expanded)
%              Number of equality atoms :   25 (  64 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f598,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f107,f148,f162,f177,f184,f185,f191,f204,f213,f244,f252,f299,f313,f326,f335,f465,f509,f571,f573,f580,f595])).

fof(f595,plain,
    ( spl9_42
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f558,f507,f459])).

fof(f459,plain,
    ( spl9_42
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f507,plain,
    ( spl9_45
  <=> ! [X0] : r1_tarski(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f558,plain,
    ( v1_xboole_0(sK0)
    | ~ spl9_45 ),
    inference(resolution,[],[f545,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f545,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK0)
    | ~ spl9_45 ),
    inference(resolution,[],[f508,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f508,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f507])).

fof(f580,plain,
    ( spl9_3
    | ~ spl9_29
    | ~ spl9_4
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f575,f96,f104,f323,f100])).

fof(f100,plain,
    ( spl9_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f323,plain,
    ( spl9_29
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f104,plain,
    ( spl9_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f96,plain,
    ( spl9_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f575,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_partfun1(sK2,sK0)
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl9_2 ),
    inference(resolution,[],[f97,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f573,plain,
    ( spl9_3
    | ~ spl9_43 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | spl9_3
    | ~ spl9_43 ),
    inference(resolution,[],[f464,f102])).

fof(f102,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f464,plain,
    ( ! [X2] : v1_funct_2(sK2,sK0,X2)
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl9_43
  <=> ! [X2] : v1_funct_2(sK2,sK0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f571,plain,
    ( ~ spl9_11
    | spl9_2
    | ~ spl9_15
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f570,f241,f210,f96,f181])).

fof(f181,plain,
    ( spl9_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f210,plain,
    ( spl9_15
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f241,plain,
    ( spl9_20
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f570,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl9_15
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f568,f243])).

fof(f243,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f241])).

fof(f568,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl9_15 ),
    inference(resolution,[],[f270,f212])).

fof(f212,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f210])).

fof(f270,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_relat_1(X3),X4)
      | ~ v1_relat_1(X3)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X3),X4))) ) ),
    inference(resolution,[],[f55,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f509,plain,
    ( ~ spl9_11
    | spl9_45
    | ~ spl9_20
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f505,f306,f241,f507,f181])).

fof(f306,plain,
    ( spl9_26
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f505,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_20
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f504,f243])).

fof(f504,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(sK2),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_26 ),
    inference(resolution,[],[f500,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f500,plain,
    ( ! [X6] : v4_relat_1(sK2,X6)
    | ~ spl9_26 ),
    inference(resolution,[],[f454,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f454,plain,
    ( ! [X2] : m1_subset_1(sK2,k1_zfmisc_1(X2))
    | ~ spl9_26 ),
    inference(resolution,[],[f449,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f449,plain,
    ( ! [X1] : r1_tarski(sK2,X1)
    | ~ spl9_26 ),
    inference(resolution,[],[f308,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f308,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f306])).

fof(f465,plain,
    ( ~ spl9_42
    | spl9_43
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f457,f333,f463,f459])).

fof(f333,plain,
    ( spl9_30
  <=> ! [X0] :
        ( v1_funct_2(sK2,sK0,X0)
        | r2_hidden(sK5(sK0,X0,sK2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f457,plain,
    ( ! [X2] :
        ( v1_funct_2(sK2,sK0,X2)
        | ~ v1_xboole_0(sK0) )
    | ~ spl9_30 ),
    inference(resolution,[],[f334,f41])).

fof(f334,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0,sK2),sK0)
        | v1_funct_2(sK2,sK0,X0) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f333])).

fof(f335,plain,
    ( ~ spl9_11
    | spl9_30
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f331,f241,f104,f333,f181])).

fof(f331,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,sK0,X0)
        | r2_hidden(sK5(sK0,X0,sK2),sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f330,f243])).

fof(f330,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0,sK2),sK0)
        | ~ v1_relat_1(sK2)
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) )
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f329,f243])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | r2_hidden(sK5(k1_relat_1(sK2),X0,sK2),k1_relat_1(sK2))
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f78,f105])).

fof(f105,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | v1_funct_2(X2,k1_relat_1(X2),X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK5(X0,X1,X2),X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f326,plain,
    ( spl9_29
    | ~ spl9_21
    | ~ spl9_4
    | spl9_27
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f319,f296,f310,f104,f249,f323])).

fof(f249,plain,
    ( spl9_21
  <=> v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f310,plain,
    ( spl9_27
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f296,plain,
    ( spl9_25
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f319,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | v1_partfun1(sK2,sK0)
    | ~ spl9_25 ),
    inference(resolution,[],[f42,f298])).

fof(f298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f296])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f313,plain,
    ( spl9_26
    | ~ spl9_27
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f301,f296,f310,f306])).

fof(f301,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v1_xboole_0(sK2)
    | ~ spl9_25 ),
    inference(resolution,[],[f298,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f299,plain,
    ( spl9_25
    | ~ spl9_14
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f294,f241,f201,f296])).

fof(f201,plain,
    ( spl9_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f294,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl9_14
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f203,f243])).

fof(f203,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f252,plain,
    ( spl9_21
    | ~ spl9_12
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f245,f241,f188,f249])).

fof(f188,plain,
    ( spl9_12
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f245,plain,
    ( v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ spl9_12
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f190,f243])).

fof(f190,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f188])).

fof(f244,plain,
    ( spl9_20
    | ~ spl9_1
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f239,f174,f91,f241])).

fof(f91,plain,
    ( spl9_1
  <=> r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f174,plain,
    ( spl9_10
  <=> sK2 = sK7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f239,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl9_1
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f236,f176])).

fof(f176,plain,
    ( sK2 = sK7(sK0,sK1,sK2)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f236,plain,
    ( sK0 = k1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f85,f93])).

fof(f93,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | k1_relat_1(sK7(X0,X1,X3)) = X0 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relat_1(sK7(X0,X1,X3)) = X0
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f213,plain,
    ( spl9_15
    | ~ spl9_1
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f208,f174,f91,f210])).

fof(f208,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl9_1
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f205,f176])).

fof(f205,plain,
    ( r1_tarski(k2_relat_1(sK7(sK0,sK1,sK2)),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f84,f93])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X1)
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f204,plain,
    ( spl9_14
    | ~ spl9_11
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f199,f104,f181,f201])).

fof(f199,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl9_4 ),
    inference(resolution,[],[f39,f105])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f191,plain,
    ( spl9_12
    | ~ spl9_11
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f186,f104,f181,f188])).

fof(f186,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl9_4 ),
    inference(resolution,[],[f105,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f185,plain,
    ( spl9_4
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f179,f174,f145,f104])).

fof(f145,plain,
    ( spl9_6
  <=> v1_funct_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f179,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f147,f176])).

fof(f147,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f184,plain,
    ( spl9_11
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f178,f174,f155,f181])).

fof(f155,plain,
    ( spl9_8
  <=> v1_relat_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f178,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f156,f176])).

fof(f156,plain,
    ( v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f177,plain,
    ( spl9_10
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f170,f91,f174])).

fof(f170,plain,
    ( sK2 = sK7(sK0,sK1,sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f86,f93])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | sK7(X0,X1,X3) = X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sK7(X0,X1,X3) = X3
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f162,plain,
    ( spl9_8
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f159,f91,f155])).

fof(f159,plain,
    ( v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f88,f93])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | v1_relat_1(sK7(X0,X1,X3)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_relat_1(sK7(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f148,plain,
    ( spl9_6
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f141,f91,f145])).

fof(f141,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f87,f93])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | v1_funct_1(sK7(X0,X1,X3)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK7(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f107,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f36,f104,f100,f96])).

fof(f36,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f94,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f37,f91])).

fof(f37,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:32:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (31567)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (31584)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (31561)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (31568)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (31577)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (31563)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (31565)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (31564)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (31562)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (31589)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (31582)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (31575)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (31571)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (31590)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (31588)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (31583)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (31578)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (31583)Refutation not found, incomplete strategy% (31583)------------------------------
% 0.20/0.54  % (31583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31583)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31583)Memory used [KB]: 10746
% 0.20/0.54  % (31583)Time elapsed: 0.139 s
% 0.20/0.54  % (31583)------------------------------
% 0.20/0.54  % (31583)------------------------------
% 0.20/0.55  % (31580)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (31572)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (31573)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (31569)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (31579)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (31566)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (31581)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (31581)Refutation not found, incomplete strategy% (31581)------------------------------
% 0.20/0.55  % (31581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31581)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31581)Memory used [KB]: 10746
% 0.20/0.55  % (31581)Time elapsed: 0.149 s
% 0.20/0.55  % (31581)------------------------------
% 0.20/0.55  % (31581)------------------------------
% 0.20/0.55  % (31586)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (31570)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (31576)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (31587)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (31574)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.57  % (31577)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (31585)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.63/0.57  % SZS output start Proof for theBenchmark
% 1.63/0.57  fof(f598,plain,(
% 1.63/0.57    $false),
% 1.63/0.57    inference(avatar_sat_refutation,[],[f94,f107,f148,f162,f177,f184,f185,f191,f204,f213,f244,f252,f299,f313,f326,f335,f465,f509,f571,f573,f580,f595])).
% 1.63/0.57  fof(f595,plain,(
% 1.63/0.57    spl9_42 | ~spl9_45),
% 1.63/0.57    inference(avatar_split_clause,[],[f558,f507,f459])).
% 1.63/0.57  fof(f459,plain,(
% 1.63/0.57    spl9_42 <=> v1_xboole_0(sK0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 1.63/0.57  fof(f507,plain,(
% 1.63/0.57    spl9_45 <=> ! [X0] : r1_tarski(sK0,X0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 1.63/0.57  fof(f558,plain,(
% 1.63/0.57    v1_xboole_0(sK0) | ~spl9_45),
% 1.63/0.57    inference(resolution,[],[f545,f40])).
% 1.63/0.57  fof(f40,plain,(
% 1.63/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f1])).
% 1.63/0.57  fof(f1,axiom,(
% 1.63/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.63/0.57  fof(f545,plain,(
% 1.63/0.57    ( ! [X6] : (~r2_hidden(X6,sK0)) ) | ~spl9_45),
% 1.63/0.57    inference(resolution,[],[f508,f54])).
% 1.63/0.57  fof(f54,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f27])).
% 1.63/0.57  fof(f27,plain,(
% 1.63/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.63/0.57    inference(ennf_transformation,[],[f6])).
% 1.63/0.57  fof(f6,axiom,(
% 1.63/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.63/0.57  fof(f508,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl9_45),
% 1.63/0.57    inference(avatar_component_clause,[],[f507])).
% 1.63/0.57  fof(f580,plain,(
% 1.63/0.57    spl9_3 | ~spl9_29 | ~spl9_4 | ~spl9_2),
% 1.63/0.57    inference(avatar_split_clause,[],[f575,f96,f104,f323,f100])).
% 1.63/0.57  fof(f100,plain,(
% 1.63/0.57    spl9_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.63/0.57  fof(f323,plain,(
% 1.63/0.57    spl9_29 <=> v1_partfun1(sK2,sK0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 1.63/0.57  fof(f104,plain,(
% 1.63/0.57    spl9_4 <=> v1_funct_1(sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.63/0.57  fof(f96,plain,(
% 1.63/0.57    spl9_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.63/0.57  fof(f575,plain,(
% 1.63/0.57    ~v1_funct_1(sK2) | ~v1_partfun1(sK2,sK0) | v1_funct_2(sK2,sK0,sK1) | ~spl9_2),
% 1.63/0.57    inference(resolution,[],[f97,f58])).
% 1.63/0.57  fof(f58,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f33])).
% 1.63/0.57  fof(f33,plain,(
% 1.63/0.57    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.57    inference(flattening,[],[f32])).
% 1.63/0.57  fof(f32,plain,(
% 1.63/0.57    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.57    inference(ennf_transformation,[],[f11])).
% 1.63/0.57  fof(f11,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 1.63/0.57  fof(f97,plain,(
% 1.63/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_2),
% 1.63/0.57    inference(avatar_component_clause,[],[f96])).
% 1.63/0.57  fof(f573,plain,(
% 1.63/0.57    spl9_3 | ~spl9_43),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f572])).
% 1.63/0.57  fof(f572,plain,(
% 1.63/0.57    $false | (spl9_3 | ~spl9_43)),
% 1.63/0.57    inference(resolution,[],[f464,f102])).
% 1.63/0.57  fof(f102,plain,(
% 1.63/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl9_3),
% 1.63/0.57    inference(avatar_component_clause,[],[f100])).
% 1.63/0.57  fof(f464,plain,(
% 1.63/0.57    ( ! [X2] : (v1_funct_2(sK2,sK0,X2)) ) | ~spl9_43),
% 1.63/0.57    inference(avatar_component_clause,[],[f463])).
% 1.63/0.57  fof(f463,plain,(
% 1.63/0.57    spl9_43 <=> ! [X2] : v1_funct_2(sK2,sK0,X2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 1.63/0.57  fof(f571,plain,(
% 1.63/0.57    ~spl9_11 | spl9_2 | ~spl9_15 | ~spl9_20),
% 1.63/0.57    inference(avatar_split_clause,[],[f570,f241,f210,f96,f181])).
% 1.63/0.57  fof(f181,plain,(
% 1.63/0.57    spl9_11 <=> v1_relat_1(sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.63/0.57  fof(f210,plain,(
% 1.63/0.57    spl9_15 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.63/0.57  fof(f241,plain,(
% 1.63/0.57    spl9_20 <=> sK0 = k1_relat_1(sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.63/0.57  fof(f570,plain,(
% 1.63/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_relat_1(sK2) | (~spl9_15 | ~spl9_20)),
% 1.63/0.57    inference(forward_demodulation,[],[f568,f243])).
% 1.63/0.57  fof(f243,plain,(
% 1.63/0.57    sK0 = k1_relat_1(sK2) | ~spl9_20),
% 1.63/0.57    inference(avatar_component_clause,[],[f241])).
% 1.63/0.57  fof(f568,plain,(
% 1.63/0.57    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl9_15),
% 1.63/0.57    inference(resolution,[],[f270,f212])).
% 1.63/0.57  fof(f212,plain,(
% 1.63/0.57    r1_tarski(k2_relat_1(sK2),sK1) | ~spl9_15),
% 1.63/0.57    inference(avatar_component_clause,[],[f210])).
% 1.63/0.57  fof(f270,plain,(
% 1.63/0.57    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(X3),X4) | ~v1_relat_1(X3) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X3),X4)))) )),
% 1.63/0.57    inference(resolution,[],[f55,f75])).
% 1.63/0.57  fof(f75,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.63/0.57    inference(equality_resolution,[],[f47])).
% 1.63/0.57  fof(f47,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.63/0.57    inference(cnf_transformation,[],[f3])).
% 1.63/0.57  fof(f3,axiom,(
% 1.63/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.63/0.57  fof(f55,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f29])).
% 1.63/0.57  fof(f29,plain,(
% 1.63/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.63/0.57    inference(flattening,[],[f28])).
% 1.63/0.57  fof(f28,plain,(
% 1.63/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.63/0.57    inference(ennf_transformation,[],[f10])).
% 1.63/0.57  fof(f10,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.63/0.57  fof(f509,plain,(
% 1.63/0.57    ~spl9_11 | spl9_45 | ~spl9_20 | ~spl9_26),
% 1.63/0.57    inference(avatar_split_clause,[],[f505,f306,f241,f507,f181])).
% 1.63/0.57  fof(f306,plain,(
% 1.63/0.57    spl9_26 <=> v1_xboole_0(sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.63/0.57  fof(f505,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(sK0,X0) | ~v1_relat_1(sK2)) ) | (~spl9_20 | ~spl9_26)),
% 1.63/0.57    inference(forward_demodulation,[],[f504,f243])).
% 1.63/0.57  fof(f504,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0) | ~v1_relat_1(sK2)) ) | ~spl9_26),
% 1.63/0.57    inference(resolution,[],[f500,f44])).
% 1.63/0.57  fof(f44,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f24])).
% 1.63/0.57  fof(f24,plain,(
% 1.63/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.63/0.57    inference(ennf_transformation,[],[f5])).
% 1.63/0.57  fof(f5,axiom,(
% 1.63/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.63/0.57  fof(f500,plain,(
% 1.63/0.57    ( ! [X6] : (v4_relat_1(sK2,X6)) ) | ~spl9_26),
% 1.63/0.57    inference(resolution,[],[f454,f57])).
% 1.63/0.57  fof(f57,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f31])).
% 1.63/0.57  fof(f31,plain,(
% 1.63/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.57    inference(ennf_transformation,[],[f18])).
% 1.63/0.57  fof(f18,plain,(
% 1.63/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.63/0.57    inference(pure_predicate_removal,[],[f8])).
% 1.63/0.57  fof(f8,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.63/0.57  fof(f454,plain,(
% 1.63/0.57    ( ! [X2] : (m1_subset_1(sK2,k1_zfmisc_1(X2))) ) | ~spl9_26),
% 1.63/0.57    inference(resolution,[],[f449,f52])).
% 1.63/0.57  fof(f52,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f4])).
% 1.63/0.57  fof(f4,axiom,(
% 1.63/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.63/0.57  fof(f449,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(sK2,X1)) ) | ~spl9_26),
% 1.63/0.57    inference(resolution,[],[f308,f118])).
% 1.63/0.57  fof(f118,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.63/0.57    inference(resolution,[],[f50,f41])).
% 1.63/0.57  fof(f41,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f1])).
% 1.63/0.57  fof(f50,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f26])).
% 1.63/0.57  fof(f26,plain,(
% 1.63/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.63/0.57    inference(ennf_transformation,[],[f2])).
% 1.63/0.57  fof(f2,axiom,(
% 1.63/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.63/0.57  fof(f308,plain,(
% 1.63/0.57    v1_xboole_0(sK2) | ~spl9_26),
% 1.63/0.57    inference(avatar_component_clause,[],[f306])).
% 1.63/0.57  fof(f465,plain,(
% 1.63/0.57    ~spl9_42 | spl9_43 | ~spl9_30),
% 1.63/0.57    inference(avatar_split_clause,[],[f457,f333,f463,f459])).
% 1.63/0.57  fof(f333,plain,(
% 1.63/0.57    spl9_30 <=> ! [X0] : (v1_funct_2(sK2,sK0,X0) | r2_hidden(sK5(sK0,X0,sK2),sK0))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.63/0.57  fof(f457,plain,(
% 1.63/0.57    ( ! [X2] : (v1_funct_2(sK2,sK0,X2) | ~v1_xboole_0(sK0)) ) | ~spl9_30),
% 1.63/0.57    inference(resolution,[],[f334,f41])).
% 1.63/0.57  fof(f334,plain,(
% 1.63/0.57    ( ! [X0] : (r2_hidden(sK5(sK0,X0,sK2),sK0) | v1_funct_2(sK2,sK0,X0)) ) | ~spl9_30),
% 1.63/0.57    inference(avatar_component_clause,[],[f333])).
% 1.63/0.57  fof(f335,plain,(
% 1.63/0.57    ~spl9_11 | spl9_30 | ~spl9_4 | ~spl9_20),
% 1.63/0.57    inference(avatar_split_clause,[],[f331,f241,f104,f333,f181])).
% 1.63/0.57  fof(f331,plain,(
% 1.63/0.57    ( ! [X0] : (v1_funct_2(sK2,sK0,X0) | r2_hidden(sK5(sK0,X0,sK2),sK0) | ~v1_relat_1(sK2)) ) | (~spl9_4 | ~spl9_20)),
% 1.63/0.57    inference(forward_demodulation,[],[f330,f243])).
% 1.63/0.57  fof(f330,plain,(
% 1.63/0.57    ( ! [X0] : (r2_hidden(sK5(sK0,X0,sK2),sK0) | ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | (~spl9_4 | ~spl9_20)),
% 1.63/0.57    inference(forward_demodulation,[],[f329,f243])).
% 1.63/0.57  fof(f329,plain,(
% 1.63/0.57    ( ! [X0] : (~v1_relat_1(sK2) | r2_hidden(sK5(k1_relat_1(sK2),X0,sK2),k1_relat_1(sK2)) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | ~spl9_4),
% 1.63/0.57    inference(resolution,[],[f78,f105])).
% 1.63/0.57  fof(f105,plain,(
% 1.63/0.57    v1_funct_1(sK2) | ~spl9_4),
% 1.63/0.57    inference(avatar_component_clause,[],[f104])).
% 1.63/0.57  fof(f78,plain,(
% 1.63/0.57    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | v1_funct_2(X2,k1_relat_1(X2),X1)) )),
% 1.63/0.57    inference(equality_resolution,[],[f61])).
% 1.63/0.57  fof(f61,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK5(X0,X1,X2),X0) | v1_funct_2(X2,X0,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f35,plain,(
% 1.63/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.63/0.57    inference(flattening,[],[f34])).
% 1.63/0.57  fof(f34,plain,(
% 1.63/0.57    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.63/0.57    inference(ennf_transformation,[],[f15])).
% 1.63/0.57  fof(f15,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 1.63/0.57  fof(f326,plain,(
% 1.63/0.57    spl9_29 | ~spl9_21 | ~spl9_4 | spl9_27 | ~spl9_25),
% 1.63/0.57    inference(avatar_split_clause,[],[f319,f296,f310,f104,f249,f323])).
% 1.63/0.57  fof(f249,plain,(
% 1.63/0.57    spl9_21 <=> v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.63/0.57  fof(f310,plain,(
% 1.63/0.57    spl9_27 <=> v1_xboole_0(k2_relat_1(sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 1.63/0.57  fof(f296,plain,(
% 1.63/0.57    spl9_25 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 1.63/0.57  fof(f319,plain,(
% 1.63/0.57    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | v1_partfun1(sK2,sK0) | ~spl9_25),
% 1.63/0.57    inference(resolution,[],[f42,f298])).
% 1.63/0.57  fof(f298,plain,(
% 1.63/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~spl9_25),
% 1.63/0.57    inference(avatar_component_clause,[],[f296])).
% 1.63/0.57  fof(f42,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f23])).
% 1.63/0.57  fof(f23,plain,(
% 1.63/0.57    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.63/0.57    inference(flattening,[],[f22])).
% 1.63/0.57  fof(f22,plain,(
% 1.63/0.57    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.63/0.57    inference(ennf_transformation,[],[f12])).
% 1.63/0.57  fof(f12,axiom,(
% 1.63/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.63/0.57  fof(f313,plain,(
% 1.63/0.57    spl9_26 | ~spl9_27 | ~spl9_25),
% 1.63/0.57    inference(avatar_split_clause,[],[f301,f296,f310,f306])).
% 1.63/0.57  fof(f301,plain,(
% 1.63/0.57    ~v1_xboole_0(k2_relat_1(sK2)) | v1_xboole_0(sK2) | ~spl9_25),
% 1.63/0.57    inference(resolution,[],[f298,f45])).
% 1.63/0.57  fof(f45,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f25])).
% 1.63/0.57  fof(f25,plain,(
% 1.63/0.57    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.63/0.57    inference(ennf_transformation,[],[f9])).
% 1.63/0.57  fof(f9,axiom,(
% 1.63/0.57    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.63/0.57  fof(f299,plain,(
% 1.63/0.57    spl9_25 | ~spl9_14 | ~spl9_20),
% 1.63/0.57    inference(avatar_split_clause,[],[f294,f241,f201,f296])).
% 1.63/0.57  fof(f201,plain,(
% 1.63/0.57    spl9_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.63/0.57  fof(f294,plain,(
% 1.63/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | (~spl9_14 | ~spl9_20)),
% 1.63/0.57    inference(forward_demodulation,[],[f203,f243])).
% 1.63/0.57  fof(f203,plain,(
% 1.63/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl9_14),
% 1.63/0.57    inference(avatar_component_clause,[],[f201])).
% 1.63/0.57  fof(f252,plain,(
% 1.63/0.57    spl9_21 | ~spl9_12 | ~spl9_20),
% 1.63/0.57    inference(avatar_split_clause,[],[f245,f241,f188,f249])).
% 1.63/0.57  fof(f188,plain,(
% 1.63/0.57    spl9_12 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.63/0.57  fof(f245,plain,(
% 1.63/0.57    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | (~spl9_12 | ~spl9_20)),
% 1.63/0.57    inference(backward_demodulation,[],[f190,f243])).
% 1.63/0.57  fof(f190,plain,(
% 1.63/0.57    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl9_12),
% 1.63/0.57    inference(avatar_component_clause,[],[f188])).
% 1.63/0.57  fof(f244,plain,(
% 1.63/0.57    spl9_20 | ~spl9_1 | ~spl9_10),
% 1.63/0.57    inference(avatar_split_clause,[],[f239,f174,f91,f241])).
% 1.63/0.57  fof(f91,plain,(
% 1.63/0.57    spl9_1 <=> r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.63/0.57  fof(f174,plain,(
% 1.63/0.57    spl9_10 <=> sK2 = sK7(sK0,sK1,sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.63/0.57  fof(f239,plain,(
% 1.63/0.57    sK0 = k1_relat_1(sK2) | (~spl9_1 | ~spl9_10)),
% 1.63/0.57    inference(forward_demodulation,[],[f236,f176])).
% 1.63/0.57  fof(f176,plain,(
% 1.63/0.57    sK2 = sK7(sK0,sK1,sK2) | ~spl9_10),
% 1.63/0.57    inference(avatar_component_clause,[],[f174])).
% 1.63/0.57  fof(f236,plain,(
% 1.63/0.57    sK0 = k1_relat_1(sK7(sK0,sK1,sK2)) | ~spl9_1),
% 1.63/0.57    inference(resolution,[],[f85,f93])).
% 1.63/0.57  fof(f93,plain,(
% 1.63/0.57    r2_hidden(sK2,k1_funct_2(sK0,sK1)) | ~spl9_1),
% 1.63/0.57    inference(avatar_component_clause,[],[f91])).
% 1.63/0.57  fof(f85,plain,(
% 1.63/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | k1_relat_1(sK7(X0,X1,X3)) = X0) )),
% 1.63/0.57    inference(equality_resolution,[],[f72])).
% 1.63/0.57  fof(f72,plain,(
% 1.63/0.57    ( ! [X2,X0,X3,X1] : (k1_relat_1(sK7(X0,X1,X3)) = X0 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f13])).
% 1.63/0.57  fof(f13,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 1.63/0.57  fof(f213,plain,(
% 1.63/0.57    spl9_15 | ~spl9_1 | ~spl9_10),
% 1.63/0.57    inference(avatar_split_clause,[],[f208,f174,f91,f210])).
% 1.63/0.57  fof(f208,plain,(
% 1.63/0.57    r1_tarski(k2_relat_1(sK2),sK1) | (~spl9_1 | ~spl9_10)),
% 1.63/0.57    inference(forward_demodulation,[],[f205,f176])).
% 1.63/0.57  fof(f205,plain,(
% 1.63/0.57    r1_tarski(k2_relat_1(sK7(sK0,sK1,sK2)),sK1) | ~spl9_1),
% 1.63/0.57    inference(resolution,[],[f84,f93])).
% 1.63/0.57  fof(f84,plain,(
% 1.63/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X1)) )),
% 1.63/0.57    inference(equality_resolution,[],[f73])).
% 1.63/0.57  fof(f73,plain,(
% 1.63/0.57    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X1) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f13])).
% 1.63/0.57  fof(f204,plain,(
% 1.63/0.57    spl9_14 | ~spl9_11 | ~spl9_4),
% 1.63/0.57    inference(avatar_split_clause,[],[f199,f104,f181,f201])).
% 1.63/0.57  fof(f199,plain,(
% 1.63/0.57    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl9_4),
% 1.63/0.57    inference(resolution,[],[f39,f105])).
% 1.63/0.57  fof(f39,plain,(
% 1.63/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f21])).
% 1.63/0.57  fof(f21,plain,(
% 1.63/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.63/0.57    inference(flattening,[],[f20])).
% 1.63/0.57  fof(f20,plain,(
% 1.63/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.63/0.57    inference(ennf_transformation,[],[f14])).
% 1.63/0.57  fof(f14,axiom,(
% 1.63/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.63/0.57  fof(f191,plain,(
% 1.63/0.57    spl9_12 | ~spl9_11 | ~spl9_4),
% 1.63/0.57    inference(avatar_split_clause,[],[f186,f104,f181,f188])).
% 1.63/0.57  fof(f186,plain,(
% 1.63/0.57    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl9_4),
% 1.63/0.57    inference(resolution,[],[f105,f38])).
% 1.63/0.57  fof(f38,plain,(
% 1.63/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f21])).
% 1.63/0.57  fof(f185,plain,(
% 1.63/0.57    spl9_4 | ~spl9_6 | ~spl9_10),
% 1.63/0.57    inference(avatar_split_clause,[],[f179,f174,f145,f104])).
% 1.63/0.57  fof(f145,plain,(
% 1.63/0.57    spl9_6 <=> v1_funct_1(sK7(sK0,sK1,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.63/0.57  fof(f179,plain,(
% 1.63/0.57    v1_funct_1(sK2) | (~spl9_6 | ~spl9_10)),
% 1.63/0.57    inference(backward_demodulation,[],[f147,f176])).
% 1.63/0.57  fof(f147,plain,(
% 1.63/0.57    v1_funct_1(sK7(sK0,sK1,sK2)) | ~spl9_6),
% 1.63/0.57    inference(avatar_component_clause,[],[f145])).
% 1.63/0.57  fof(f184,plain,(
% 1.63/0.57    spl9_11 | ~spl9_8 | ~spl9_10),
% 1.63/0.57    inference(avatar_split_clause,[],[f178,f174,f155,f181])).
% 1.63/0.57  fof(f155,plain,(
% 1.63/0.57    spl9_8 <=> v1_relat_1(sK7(sK0,sK1,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.63/0.57  fof(f178,plain,(
% 1.63/0.57    v1_relat_1(sK2) | (~spl9_8 | ~spl9_10)),
% 1.63/0.57    inference(backward_demodulation,[],[f156,f176])).
% 1.63/0.57  fof(f156,plain,(
% 1.63/0.57    v1_relat_1(sK7(sK0,sK1,sK2)) | ~spl9_8),
% 1.63/0.57    inference(avatar_component_clause,[],[f155])).
% 1.63/0.57  fof(f177,plain,(
% 1.63/0.57    spl9_10 | ~spl9_1),
% 1.63/0.57    inference(avatar_split_clause,[],[f170,f91,f174])).
% 1.63/0.57  fof(f170,plain,(
% 1.63/0.57    sK2 = sK7(sK0,sK1,sK2) | ~spl9_1),
% 1.63/0.57    inference(resolution,[],[f86,f93])).
% 1.63/0.57  fof(f86,plain,(
% 1.63/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | sK7(X0,X1,X3) = X3) )),
% 1.63/0.57    inference(equality_resolution,[],[f71])).
% 1.63/0.57  fof(f71,plain,(
% 1.63/0.57    ( ! [X2,X0,X3,X1] : (sK7(X0,X1,X3) = X3 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f13])).
% 1.63/0.57  fof(f162,plain,(
% 1.63/0.57    spl9_8 | ~spl9_1),
% 1.63/0.57    inference(avatar_split_clause,[],[f159,f91,f155])).
% 1.63/0.57  fof(f159,plain,(
% 1.63/0.57    v1_relat_1(sK7(sK0,sK1,sK2)) | ~spl9_1),
% 1.63/0.57    inference(resolution,[],[f88,f93])).
% 1.63/0.57  fof(f88,plain,(
% 1.63/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | v1_relat_1(sK7(X0,X1,X3))) )),
% 1.63/0.57    inference(equality_resolution,[],[f69])).
% 1.63/0.57  fof(f69,plain,(
% 1.63/0.57    ( ! [X2,X0,X3,X1] : (v1_relat_1(sK7(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f13])).
% 1.63/0.58  fof(f148,plain,(
% 1.63/0.58    spl9_6 | ~spl9_1),
% 1.63/0.58    inference(avatar_split_clause,[],[f141,f91,f145])).
% 1.63/0.58  fof(f141,plain,(
% 1.63/0.58    v1_funct_1(sK7(sK0,sK1,sK2)) | ~spl9_1),
% 1.63/0.58    inference(resolution,[],[f87,f93])).
% 1.63/0.58  fof(f87,plain,(
% 1.63/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | v1_funct_1(sK7(X0,X1,X3))) )),
% 1.63/0.58    inference(equality_resolution,[],[f70])).
% 1.63/0.58  fof(f70,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK7(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.63/0.58    inference(cnf_transformation,[],[f13])).
% 1.63/0.58  fof(f107,plain,(
% 1.63/0.58    ~spl9_2 | ~spl9_3 | ~spl9_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f36,f104,f100,f96])).
% 1.63/0.58  fof(f36,plain,(
% 1.63/0.58    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.58    inference(cnf_transformation,[],[f19])).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f17])).
% 1.63/0.58  fof(f17,negated_conjecture,(
% 1.63/0.58    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.63/0.58    inference(negated_conjecture,[],[f16])).
% 1.63/0.58  fof(f16,conjecture,(
% 1.63/0.58    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 1.63/0.58  fof(f94,plain,(
% 1.63/0.58    spl9_1),
% 1.63/0.58    inference(avatar_split_clause,[],[f37,f91])).
% 1.63/0.58  fof(f37,plain,(
% 1.63/0.58    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.63/0.58    inference(cnf_transformation,[],[f19])).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (31577)------------------------------
% 1.63/0.58  % (31577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (31577)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (31577)Memory used [KB]: 11129
% 1.63/0.58  % (31577)Time elapsed: 0.164 s
% 1.63/0.58  % (31577)------------------------------
% 1.63/0.58  % (31577)------------------------------
% 1.63/0.58  % (31560)Success in time 0.219 s
%------------------------------------------------------------------------------
