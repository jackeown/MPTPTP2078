%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:09 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 803 expanded)
%              Number of leaves         :   25 ( 203 expanded)
%              Depth                    :   17
%              Number of atoms          :  504 (4772 expanded)
%              Number of equality atoms :  108 (1134 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f115,f161,f295,f578,f996,f1024,f1042,f1147,f1155,f1172])).

fof(f1172,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f1171])).

fof(f1171,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f1170,f1128])).

fof(f1128,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f1076,f298])).

fof(f298,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f297,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f297,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f158,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f158,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_11
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1076,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1053,f87])).

fof(f1053,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f50,f109])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f39])).

fof(f39,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f1170,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1169,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f1169,plain,
    ( ~ m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1168,f298])).

fof(f1168,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1167,f1103])).

fof(f1103,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f1102,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1102,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f300,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f300,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f51,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f51,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1167,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1166,f87])).

fof(f1166,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f609,f109])).

fof(f609,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(backward_demodulation,[],[f105,f134])).

fof(f134,plain,(
    ! [X1] : k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) ),
    inference(subsumption_resolution,[],[f127,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f127,plain,(
    ! [X1] :
      ( k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f50,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f105,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1155,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1150,f1142])).

fof(f1142,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1108,f298])).

fof(f1108,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1052,f114])).

fof(f1052,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f49,f109])).

fof(f49,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1150,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f1149,f1103])).

fof(f1149,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f322,f109])).

fof(f322,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,sK1)
    | spl4_2
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f321,f56])).

fof(f321,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f177,f222])).

fof(f222,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f177,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f101,f134])).

fof(f101,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1147,plain,
    ( ~ spl4_4
    | ~ spl4_11
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f1146])).

fof(f1146,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f221,f298])).

fof(f221,plain,
    ( k1_xboole_0 != sK3
    | spl4_12 ),
    inference(avatar_component_clause,[],[f220])).

fof(f1042,plain,
    ( spl4_18
    | spl4_4 ),
    inference(avatar_split_clause,[],[f397,f108,f271])).

fof(f271,plain,
    ( spl4_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f397,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f390,f49])).

fof(f390,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f50,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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

fof(f1024,plain,
    ( spl4_2
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f1023])).

fof(f1023,plain,
    ( $false
    | spl4_2
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f1022,f931])).

fof(f931,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_18 ),
    inference(resolution,[],[f685,f196])).

fof(f196,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f195,f186])).

fof(f186,plain,(
    ! [X7] : v1_relat_1(k7_relat_1(sK3,X7)) ),
    inference(resolution,[],[f180,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f180,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f179,f48])).

fof(f179,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f178,f50])).

fof(f178,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f84,f134])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f195,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f184,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f184,plain,(
    ! [X5] : v5_relat_1(k7_relat_1(sK3,X5),sK1) ),
    inference(resolution,[],[f180,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f685,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) )
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f684,f186])).

fof(f684,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f681,f176])).

fof(f176,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f133,f134])).

fof(f133,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f126,f48])).

fof(f126,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f50,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f681,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_18 ),
    inference(superposition,[],[f63,f663])).

fof(f663,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_18 ),
    inference(resolution,[],[f591,f51])).

fof(f591,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f586,f131])).

fof(f131,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f73])).

fof(f586,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | ~ spl4_18 ),
    inference(superposition,[],[f59,f583])).

fof(f583,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f130,f273])).

fof(f273,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f271])).

fof(f130,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f50,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1022,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f101,f134])).

fof(f996,plain,
    ( spl4_3
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f995])).

fof(f995,plain,
    ( $false
    | spl4_3
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f985,f196])).

fof(f985,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_3
    | ~ spl4_18 ),
    inference(resolution,[],[f687,f609])).

fof(f687,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f686,f186])).

fof(f686,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f682,f176])).

fof(f682,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_18 ),
    inference(superposition,[],[f64,f663])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f578,plain,
    ( ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f577,f156,f152])).

fof(f152,plain,
    ( spl4_10
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f577,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    inference(resolution,[],[f132,f67])).

fof(f132,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f295,plain,
    ( ~ spl4_4
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f293,f55])).

fof(f293,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_4
    | spl4_10 ),
    inference(forward_demodulation,[],[f282,f87])).

fof(f282,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | ~ spl4_4
    | spl4_10 ),
    inference(backward_demodulation,[],[f154,f109])).

fof(f154,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f161,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f133,f97])).

fof(f97,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f115,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f52,f112,f108])).

fof(f52,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f106,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f103,f99,f95])).

fof(f53,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:37:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (16844)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (16847)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (16852)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (16873)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (16871)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (16846)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (16857)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (16848)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (16850)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (16864)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (16855)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (16851)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (16872)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (16854)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (16843)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (16842)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (16870)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (16853)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (16845)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (16862)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (16869)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (16867)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (16874)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.37/0.55  % (16843)Refutation found. Thanks to Tanya!
% 1.37/0.55  % SZS status Theorem for theBenchmark
% 1.37/0.55  % (16860)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.37/0.56  % (16875)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.37/0.56  % (16849)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.37/0.56  % SZS output start Proof for theBenchmark
% 1.37/0.56  fof(f1182,plain,(
% 1.37/0.56    $false),
% 1.37/0.56    inference(avatar_sat_refutation,[],[f106,f115,f161,f295,f578,f996,f1024,f1042,f1147,f1155,f1172])).
% 1.37/0.56  fof(f1172,plain,(
% 1.37/0.56    spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f1171])).
% 1.37/0.56  fof(f1171,plain,(
% 1.37/0.56    $false | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.37/0.56    inference(subsumption_resolution,[],[f1170,f1128])).
% 1.37/0.56  fof(f1128,plain,(
% 1.37/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | ~spl4_11)),
% 1.37/0.56    inference(backward_demodulation,[],[f1076,f298])).
% 1.37/0.56  fof(f298,plain,(
% 1.37/0.56    k1_xboole_0 = sK3 | (~spl4_4 | ~spl4_11)),
% 1.37/0.56    inference(forward_demodulation,[],[f297,f87])).
% 1.37/0.56  fof(f87,plain,(
% 1.37/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.37/0.56    inference(equality_resolution,[],[f72])).
% 1.37/0.56  fof(f72,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.37/0.56    inference(cnf_transformation,[],[f46])).
% 1.37/0.56  fof(f46,plain,(
% 1.37/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.37/0.56    inference(flattening,[],[f45])).
% 1.37/0.56  fof(f45,plain,(
% 1.37/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.37/0.56    inference(nnf_transformation,[],[f4])).
% 1.37/0.56  fof(f4,axiom,(
% 1.37/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.37/0.56  fof(f297,plain,(
% 1.37/0.56    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl4_4 | ~spl4_11)),
% 1.37/0.56    inference(forward_demodulation,[],[f158,f109])).
% 1.37/0.56  fof(f109,plain,(
% 1.37/0.56    k1_xboole_0 = sK1 | ~spl4_4),
% 1.37/0.56    inference(avatar_component_clause,[],[f108])).
% 1.37/0.56  fof(f108,plain,(
% 1.37/0.56    spl4_4 <=> k1_xboole_0 = sK1),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.37/0.56  fof(f158,plain,(
% 1.37/0.56    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl4_11),
% 1.37/0.56    inference(avatar_component_clause,[],[f156])).
% 1.37/0.56  fof(f156,plain,(
% 1.37/0.56    spl4_11 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.37/0.56  fof(f1076,plain,(
% 1.37/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_4),
% 1.37/0.56    inference(forward_demodulation,[],[f1053,f87])).
% 1.37/0.56  fof(f1053,plain,(
% 1.37/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_4),
% 1.37/0.56    inference(backward_demodulation,[],[f50,f109])).
% 1.37/0.56  fof(f50,plain,(
% 1.37/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.37/0.56    inference(cnf_transformation,[],[f40])).
% 1.37/0.56  fof(f40,plain,(
% 1.37/0.56    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.37/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f39])).
% 1.37/0.56  fof(f39,plain,(
% 1.37/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.37/0.56    introduced(choice_axiom,[])).
% 1.37/0.56  fof(f22,plain,(
% 1.37/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.37/0.56    inference(flattening,[],[f21])).
% 1.37/0.56  fof(f21,plain,(
% 1.37/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.37/0.56    inference(ennf_transformation,[],[f19])).
% 1.37/0.56  fof(f19,negated_conjecture,(
% 1.37/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.37/0.56    inference(negated_conjecture,[],[f18])).
% 1.37/0.56  fof(f18,conjecture,(
% 1.37/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.37/0.56  fof(f1170,plain,(
% 1.37/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.37/0.56    inference(forward_demodulation,[],[f1169,f56])).
% 1.37/0.56  fof(f56,plain,(
% 1.37/0.56    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f8])).
% 1.37/0.56  fof(f8,axiom,(
% 1.37/0.56    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 1.37/0.56  fof(f1169,plain,(
% 1.37/0.56    ~m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.37/0.56    inference(forward_demodulation,[],[f1168,f298])).
% 1.37/0.56  fof(f1168,plain,(
% 1.37/0.56    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.37/0.56    inference(forward_demodulation,[],[f1167,f1103])).
% 1.37/0.56  fof(f1103,plain,(
% 1.37/0.56    k1_xboole_0 = sK2 | ~spl4_5),
% 1.37/0.56    inference(subsumption_resolution,[],[f1102,f55])).
% 1.37/0.56  fof(f55,plain,(
% 1.37/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f3])).
% 1.37/0.56  fof(f3,axiom,(
% 1.37/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.37/0.56  fof(f1102,plain,(
% 1.37/0.56    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl4_5),
% 1.37/0.56    inference(resolution,[],[f300,f67])).
% 1.37/0.56  fof(f67,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f43])).
% 1.37/0.56  fof(f43,plain,(
% 1.37/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.56    inference(flattening,[],[f42])).
% 1.37/0.56  fof(f42,plain,(
% 1.37/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.56    inference(nnf_transformation,[],[f2])).
% 1.37/0.56  fof(f2,axiom,(
% 1.37/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.56  fof(f300,plain,(
% 1.37/0.56    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.37/0.56    inference(backward_demodulation,[],[f51,f114])).
% 1.37/0.56  fof(f114,plain,(
% 1.37/0.56    k1_xboole_0 = sK0 | ~spl4_5),
% 1.37/0.56    inference(avatar_component_clause,[],[f112])).
% 1.37/0.56  fof(f112,plain,(
% 1.37/0.56    spl4_5 <=> k1_xboole_0 = sK0),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.37/0.56  fof(f51,plain,(
% 1.37/0.56    r1_tarski(sK2,sK0)),
% 1.37/0.56    inference(cnf_transformation,[],[f40])).
% 1.37/0.56  fof(f1167,plain,(
% 1.37/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4)),
% 1.37/0.56    inference(forward_demodulation,[],[f1166,f87])).
% 1.37/0.56  fof(f1166,plain,(
% 1.37/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (spl4_3 | ~spl4_4)),
% 1.37/0.56    inference(forward_demodulation,[],[f609,f109])).
% 1.37/0.56  fof(f609,plain,(
% 1.37/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.37/0.56    inference(backward_demodulation,[],[f105,f134])).
% 1.37/0.56  fof(f134,plain,(
% 1.37/0.56    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)) )),
% 1.37/0.56    inference(subsumption_resolution,[],[f127,f48])).
% 1.37/0.56  fof(f48,plain,(
% 1.37/0.56    v1_funct_1(sK3)),
% 1.37/0.56    inference(cnf_transformation,[],[f40])).
% 1.37/0.56  fof(f127,plain,(
% 1.37/0.56    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.37/0.56    inference(resolution,[],[f50,f82])).
% 1.37/0.56  fof(f82,plain,(
% 1.37/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f36])).
% 1.37/0.56  fof(f36,plain,(
% 1.37/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.37/0.56    inference(flattening,[],[f35])).
% 1.37/0.56  fof(f35,plain,(
% 1.37/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.37/0.56    inference(ennf_transformation,[],[f16])).
% 1.37/0.56  fof(f16,axiom,(
% 1.37/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.37/0.56  fof(f105,plain,(
% 1.37/0.56    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.37/0.56    inference(avatar_component_clause,[],[f103])).
% 1.37/0.56  fof(f103,plain,(
% 1.37/0.56    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.37/0.56  fof(f1155,plain,(
% 1.37/0.56    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f1154])).
% 1.37/0.56  fof(f1154,plain,(
% 1.37/0.56    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12)),
% 1.37/0.56    inference(subsumption_resolution,[],[f1150,f1142])).
% 1.37/0.56  fof(f1142,plain,(
% 1.37/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.37/0.56    inference(forward_demodulation,[],[f1108,f298])).
% 1.37/0.56  fof(f1108,plain,(
% 1.37/0.56    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.37/0.56    inference(forward_demodulation,[],[f1052,f114])).
% 1.37/0.56  fof(f1052,plain,(
% 1.37/0.56    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 1.37/0.56    inference(backward_demodulation,[],[f49,f109])).
% 1.37/0.56  fof(f49,plain,(
% 1.37/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.37/0.56    inference(cnf_transformation,[],[f40])).
% 1.37/0.56  fof(f1150,plain,(
% 1.37/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_12)),
% 1.37/0.56    inference(forward_demodulation,[],[f1149,f1103])).
% 1.37/0.56  fof(f1149,plain,(
% 1.37/0.56    ~v1_funct_2(k1_xboole_0,sK2,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_12)),
% 1.37/0.56    inference(forward_demodulation,[],[f322,f109])).
% 1.37/0.56  fof(f322,plain,(
% 1.37/0.56    ~v1_funct_2(k1_xboole_0,sK2,sK1) | (spl4_2 | ~spl4_12)),
% 1.37/0.56    inference(forward_demodulation,[],[f321,f56])).
% 1.37/0.56  fof(f321,plain,(
% 1.37/0.56    ~v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1) | (spl4_2 | ~spl4_12)),
% 1.37/0.56    inference(forward_demodulation,[],[f177,f222])).
% 1.37/0.56  fof(f222,plain,(
% 1.37/0.56    k1_xboole_0 = sK3 | ~spl4_12),
% 1.37/0.56    inference(avatar_component_clause,[],[f220])).
% 1.37/0.56  fof(f220,plain,(
% 1.37/0.56    spl4_12 <=> k1_xboole_0 = sK3),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.37/0.56  fof(f177,plain,(
% 1.37/0.56    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.37/0.56    inference(backward_demodulation,[],[f101,f134])).
% 1.37/0.56  fof(f101,plain,(
% 1.37/0.56    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.37/0.56    inference(avatar_component_clause,[],[f99])).
% 1.37/0.56  fof(f99,plain,(
% 1.37/0.56    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.37/0.56  fof(f1147,plain,(
% 1.37/0.56    ~spl4_4 | ~spl4_11 | spl4_12),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f1146])).
% 1.37/0.57  fof(f1146,plain,(
% 1.37/0.57    $false | (~spl4_4 | ~spl4_11 | spl4_12)),
% 1.37/0.57    inference(subsumption_resolution,[],[f221,f298])).
% 1.37/0.57  fof(f221,plain,(
% 1.37/0.57    k1_xboole_0 != sK3 | spl4_12),
% 1.37/0.57    inference(avatar_component_clause,[],[f220])).
% 1.37/0.57  fof(f1042,plain,(
% 1.37/0.57    spl4_18 | spl4_4),
% 1.37/0.57    inference(avatar_split_clause,[],[f397,f108,f271])).
% 1.37/0.57  fof(f271,plain,(
% 1.37/0.57    spl4_18 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.37/0.57  fof(f397,plain,(
% 1.37/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.37/0.57    inference(subsumption_resolution,[],[f390,f49])).
% 1.37/0.57  fof(f390,plain,(
% 1.37/0.57    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.37/0.57    inference(resolution,[],[f50,f76])).
% 1.37/0.57  fof(f76,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.37/0.57    inference(cnf_transformation,[],[f47])).
% 1.37/0.57  fof(f47,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(nnf_transformation,[],[f34])).
% 1.37/0.57  fof(f34,plain,(
% 1.37/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(flattening,[],[f33])).
% 1.37/0.57  fof(f33,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(ennf_transformation,[],[f14])).
% 1.37/0.57  fof(f14,axiom,(
% 1.37/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.37/0.57  fof(f1024,plain,(
% 1.37/0.57    spl4_2 | ~spl4_18),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f1023])).
% 1.37/0.57  fof(f1023,plain,(
% 1.37/0.57    $false | (spl4_2 | ~spl4_18)),
% 1.37/0.57    inference(subsumption_resolution,[],[f1022,f931])).
% 1.37/0.57  fof(f931,plain,(
% 1.37/0.57    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_18),
% 1.37/0.57    inference(resolution,[],[f685,f196])).
% 1.37/0.57  fof(f196,plain,(
% 1.37/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.37/0.57    inference(subsumption_resolution,[],[f195,f186])).
% 1.37/0.57  fof(f186,plain,(
% 1.37/0.57    ( ! [X7] : (v1_relat_1(k7_relat_1(sK3,X7))) )),
% 1.37/0.57    inference(resolution,[],[f180,f73])).
% 1.37/0.57  fof(f73,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f30])).
% 1.37/0.57  fof(f30,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(ennf_transformation,[],[f11])).
% 1.37/0.57  fof(f11,axiom,(
% 1.37/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.37/0.57  fof(f180,plain,(
% 1.37/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.37/0.57    inference(subsumption_resolution,[],[f179,f48])).
% 1.37/0.57  fof(f179,plain,(
% 1.37/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.37/0.57    inference(subsumption_resolution,[],[f178,f50])).
% 1.37/0.57  fof(f178,plain,(
% 1.37/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.37/0.57    inference(superposition,[],[f84,f134])).
% 1.37/0.57  fof(f84,plain,(
% 1.37/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f38])).
% 1.37/0.57  fof(f38,plain,(
% 1.37/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.37/0.57    inference(flattening,[],[f37])).
% 1.37/0.57  fof(f37,plain,(
% 1.37/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.37/0.57    inference(ennf_transformation,[],[f15])).
% 1.37/0.57  fof(f15,axiom,(
% 1.37/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.37/0.57  fof(f195,plain,(
% 1.37/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.37/0.57    inference(resolution,[],[f184,f60])).
% 1.37/0.57  fof(f60,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f41])).
% 1.37/0.57  fof(f41,plain,(
% 1.37/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.37/0.57    inference(nnf_transformation,[],[f27])).
% 1.37/0.57  fof(f27,plain,(
% 1.37/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.37/0.57    inference(ennf_transformation,[],[f6])).
% 1.37/0.57  fof(f6,axiom,(
% 1.37/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.37/0.57  fof(f184,plain,(
% 1.37/0.57    ( ! [X5] : (v5_relat_1(k7_relat_1(sK3,X5),sK1)) )),
% 1.37/0.57    inference(resolution,[],[f180,f75])).
% 1.37/0.57  fof(f75,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f32])).
% 1.37/0.57  fof(f32,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(ennf_transformation,[],[f20])).
% 1.37/0.57  fof(f20,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.37/0.57    inference(pure_predicate_removal,[],[f12])).
% 1.37/0.57  fof(f12,axiom,(
% 1.37/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.37/0.57  fof(f685,plain,(
% 1.37/0.57    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)) ) | ~spl4_18),
% 1.37/0.57    inference(subsumption_resolution,[],[f684,f186])).
% 1.37/0.57  fof(f684,plain,(
% 1.37/0.57    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_18),
% 1.37/0.57    inference(subsumption_resolution,[],[f681,f176])).
% 1.37/0.57  fof(f176,plain,(
% 1.37/0.57    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.37/0.57    inference(backward_demodulation,[],[f133,f134])).
% 1.37/0.57  fof(f133,plain,(
% 1.37/0.57    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.37/0.57    inference(subsumption_resolution,[],[f126,f48])).
% 1.37/0.57  fof(f126,plain,(
% 1.37/0.57    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.37/0.57    inference(resolution,[],[f50,f83])).
% 1.37/0.57  fof(f83,plain,(
% 1.37/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f38])).
% 1.37/0.57  fof(f681,plain,(
% 1.37/0.57    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_18),
% 1.37/0.57    inference(superposition,[],[f63,f663])).
% 1.37/0.57  fof(f663,plain,(
% 1.37/0.57    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_18),
% 1.37/0.57    inference(resolution,[],[f591,f51])).
% 1.37/0.57  fof(f591,plain,(
% 1.37/0.57    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl4_18),
% 1.37/0.57    inference(subsumption_resolution,[],[f586,f131])).
% 1.37/0.57  fof(f131,plain,(
% 1.37/0.57    v1_relat_1(sK3)),
% 1.37/0.57    inference(resolution,[],[f50,f73])).
% 1.37/0.57  fof(f586,plain,(
% 1.37/0.57    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | ~spl4_18),
% 1.37/0.57    inference(superposition,[],[f59,f583])).
% 1.37/0.57  fof(f583,plain,(
% 1.37/0.57    sK0 = k1_relat_1(sK3) | ~spl4_18),
% 1.37/0.57    inference(forward_demodulation,[],[f130,f273])).
% 1.37/0.57  fof(f273,plain,(
% 1.37/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_18),
% 1.37/0.57    inference(avatar_component_clause,[],[f271])).
% 1.37/0.57  fof(f130,plain,(
% 1.37/0.57    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.37/0.57    inference(resolution,[],[f50,f74])).
% 1.37/0.57  fof(f74,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f31])).
% 1.37/0.57  fof(f31,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(ennf_transformation,[],[f13])).
% 1.37/0.57  fof(f13,axiom,(
% 1.37/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.37/0.57  fof(f59,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f26])).
% 1.37/0.57  fof(f26,plain,(
% 1.37/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.37/0.57    inference(flattening,[],[f25])).
% 1.37/0.57  fof(f25,plain,(
% 1.37/0.57    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.37/0.57    inference(ennf_transformation,[],[f9])).
% 1.37/0.57  fof(f9,axiom,(
% 1.37/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.37/0.57  fof(f63,plain,(
% 1.37/0.57    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f29])).
% 1.37/0.57  fof(f29,plain,(
% 1.37/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.37/0.57    inference(flattening,[],[f28])).
% 1.37/0.57  fof(f28,plain,(
% 1.37/0.57    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.37/0.57    inference(ennf_transformation,[],[f17])).
% 1.37/0.57  fof(f17,axiom,(
% 1.37/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.37/0.57  fof(f1022,plain,(
% 1.37/0.57    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.37/0.57    inference(forward_demodulation,[],[f101,f134])).
% 1.37/0.57  fof(f996,plain,(
% 1.37/0.57    spl4_3 | ~spl4_18),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f995])).
% 1.37/0.57  fof(f995,plain,(
% 1.37/0.57    $false | (spl4_3 | ~spl4_18)),
% 1.37/0.57    inference(subsumption_resolution,[],[f985,f196])).
% 1.37/0.57  fof(f985,plain,(
% 1.37/0.57    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl4_3 | ~spl4_18)),
% 1.37/0.57    inference(resolution,[],[f687,f609])).
% 1.37/0.57  fof(f687,plain,(
% 1.37/0.57    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl4_18),
% 1.37/0.57    inference(subsumption_resolution,[],[f686,f186])).
% 1.37/0.57  fof(f686,plain,(
% 1.37/0.57    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_18),
% 1.37/0.57    inference(subsumption_resolution,[],[f682,f176])).
% 1.37/0.57  fof(f682,plain,(
% 1.37/0.57    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_18),
% 1.37/0.57    inference(superposition,[],[f64,f663])).
% 1.37/0.57  fof(f64,plain,(
% 1.37/0.57    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f29])).
% 1.37/0.57  fof(f578,plain,(
% 1.37/0.57    ~spl4_10 | spl4_11),
% 1.37/0.57    inference(avatar_split_clause,[],[f577,f156,f152])).
% 1.37/0.57  fof(f152,plain,(
% 1.37/0.57    spl4_10 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.37/0.57  fof(f577,plain,(
% 1.37/0.57    sK3 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.37/0.57    inference(resolution,[],[f132,f67])).
% 1.37/0.57  fof(f132,plain,(
% 1.37/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.37/0.57    inference(resolution,[],[f50,f68])).
% 1.37/0.57  fof(f68,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f44])).
% 1.37/0.57  fof(f44,plain,(
% 1.37/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.37/0.57    inference(nnf_transformation,[],[f5])).
% 1.37/0.57  fof(f5,axiom,(
% 1.37/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.37/0.57  fof(f295,plain,(
% 1.37/0.57    ~spl4_4 | spl4_10),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f294])).
% 1.37/0.57  fof(f294,plain,(
% 1.37/0.57    $false | (~spl4_4 | spl4_10)),
% 1.37/0.57    inference(subsumption_resolution,[],[f293,f55])).
% 1.37/0.57  fof(f293,plain,(
% 1.37/0.57    ~r1_tarski(k1_xboole_0,sK3) | (~spl4_4 | spl4_10)),
% 1.37/0.57    inference(forward_demodulation,[],[f282,f87])).
% 1.37/0.57  fof(f282,plain,(
% 1.37/0.57    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | (~spl4_4 | spl4_10)),
% 1.37/0.57    inference(backward_demodulation,[],[f154,f109])).
% 1.37/0.57  fof(f154,plain,(
% 1.37/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl4_10),
% 1.37/0.57    inference(avatar_component_clause,[],[f152])).
% 1.37/0.57  fof(f161,plain,(
% 1.37/0.57    spl4_1),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f160])).
% 1.37/0.57  fof(f160,plain,(
% 1.37/0.57    $false | spl4_1),
% 1.37/0.57    inference(resolution,[],[f133,f97])).
% 1.37/0.57  fof(f97,plain,(
% 1.37/0.57    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.37/0.57    inference(avatar_component_clause,[],[f95])).
% 1.37/0.57  fof(f95,plain,(
% 1.37/0.57    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.37/0.57  fof(f115,plain,(
% 1.37/0.57    ~spl4_4 | spl4_5),
% 1.37/0.57    inference(avatar_split_clause,[],[f52,f112,f108])).
% 1.37/0.57  fof(f52,plain,(
% 1.37/0.57    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.37/0.57    inference(cnf_transformation,[],[f40])).
% 1.37/0.57  fof(f106,plain,(
% 1.37/0.57    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.37/0.57    inference(avatar_split_clause,[],[f53,f103,f99,f95])).
% 1.37/0.57  fof(f53,plain,(
% 1.37/0.57    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.37/0.57    inference(cnf_transformation,[],[f40])).
% 1.37/0.57  % SZS output end Proof for theBenchmark
% 1.37/0.57  % (16843)------------------------------
% 1.37/0.57  % (16843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (16843)Termination reason: Refutation
% 1.37/0.57  
% 1.37/0.57  % (16843)Memory used [KB]: 11001
% 1.37/0.57  % (16843)Time elapsed: 0.125 s
% 1.37/0.57  % (16843)------------------------------
% 1.37/0.57  % (16843)------------------------------
% 1.37/0.57  % (16840)Success in time 0.199 s
%------------------------------------------------------------------------------
