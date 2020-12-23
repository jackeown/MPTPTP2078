%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 260 expanded)
%              Number of leaves         :   44 ( 123 expanded)
%              Depth                    :    8
%              Number of atoms          :  425 ( 663 expanded)
%              Number of equality atoms :   56 (  96 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f129,f134,f159,f214,f225,f261,f308,f321,f344,f360,f374,f375,f382,f387,f397,f425,f595,f735,f751,f756,f831,f1032,f1052,f1104,f1191,f1203])).

fof(f1203,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK11(sK0,sK1,sK2)
    | sK0 != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK11(sK0,sK1,sK2))
    | v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1191,plain,
    ( spl14_36
    | ~ spl14_67 ),
    inference(avatar_split_clause,[],[f1182,f748,f406])).

fof(f406,plain,
    ( spl14_36
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).

fof(f748,plain,
    ( spl14_67
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_67])])).

fof(f1182,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl14_67 ),
    inference(resolution,[],[f750,f161])).

fof(f161,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f61,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f750,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl14_67 ),
    inference(avatar_component_clause,[],[f748])).

fof(f1104,plain,
    ( spl14_75
    | ~ spl14_68 ),
    inference(avatar_split_clause,[],[f1095,f753,f803])).

fof(f803,plain,
    ( spl14_75
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_75])])).

fof(f753,plain,
    ( spl14_68
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f1095,plain,
    ( k1_xboole_0 = sK2
    | ~ spl14_68 ),
    inference(resolution,[],[f755,f161])).

fof(f755,plain,
    ( v1_xboole_0(sK2)
    | ~ spl14_68 ),
    inference(avatar_component_clause,[],[f753])).

fof(f1052,plain,
    ( spl14_3
    | ~ spl14_66
    | ~ spl14_4
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f1047,f118,f126,f744,f122])).

fof(f122,plain,
    ( spl14_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f744,plain,
    ( spl14_66
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_66])])).

fof(f126,plain,
    ( spl14_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f118,plain,
    ( spl14_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f1047,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_partfun1(sK2,sK0)
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl14_2 ),
    inference(resolution,[],[f119,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f1032,plain,
    ( ~ spl14_31
    | spl14_2
    | ~ spl14_34
    | ~ spl14_38 ),
    inference(avatar_split_clause,[],[f1031,f422,f394,f118,f371])).

fof(f371,plain,
    ( spl14_31
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_31])])).

fof(f394,plain,
    ( spl14_34
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f422,plain,
    ( spl14_38
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).

fof(f1031,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl14_34
    | ~ spl14_38 ),
    inference(forward_demodulation,[],[f1028,f424])).

fof(f424,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl14_38 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1028,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl14_34 ),
    inference(resolution,[],[f512,f396])).

fof(f396,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl14_34 ),
    inference(avatar_component_clause,[],[f394])).

fof(f512,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ) ),
    inference(resolution,[],[f78,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f831,plain,
    ( sK2 != sK11(sK0,sK1,sK2)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK11(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f756,plain,
    ( spl14_68
    | ~ spl14_67
    | ~ spl14_65 ),
    inference(avatar_split_clause,[],[f739,f732,f748,f753])).

fof(f732,plain,
    ( spl14_65
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_65])])).

fof(f739,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v1_xboole_0(sK2)
    | ~ spl14_65 ),
    inference(resolution,[],[f734,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f734,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl14_65 ),
    inference(avatar_component_clause,[],[f732])).

fof(f751,plain,
    ( spl14_66
    | ~ spl14_56
    | ~ spl14_4
    | spl14_67
    | ~ spl14_65 ),
    inference(avatar_split_clause,[],[f737,f732,f748,f126,f592,f744])).

fof(f592,plain,
    ( spl14_56
  <=> v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_56])])).

fof(f737,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | v1_partfun1(sK2,sK0)
    | ~ spl14_65 ),
    inference(resolution,[],[f734,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f735,plain,
    ( spl14_65
    | ~ spl14_32
    | ~ spl14_38 ),
    inference(avatar_split_clause,[],[f730,f422,f379,f732])).

fof(f379,plain,
    ( spl14_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

% (31834)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f730,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl14_32
    | ~ spl14_38 ),
    inference(forward_demodulation,[],[f381,f424])).

fof(f381,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f379])).

fof(f595,plain,
    ( spl14_56
    | ~ spl14_33
    | ~ spl14_38 ),
    inference(avatar_split_clause,[],[f590,f422,f384,f592])).

fof(f384,plain,
    ( spl14_33
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_33])])).

fof(f590,plain,
    ( v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ spl14_33
    | ~ spl14_38 ),
    inference(forward_demodulation,[],[f386,f424])).

fof(f386,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl14_33 ),
    inference(avatar_component_clause,[],[f384])).

fof(f425,plain,
    ( spl14_38
    | ~ spl14_1
    | ~ spl14_29 ),
    inference(avatar_split_clause,[],[f420,f357,f113,f422])).

fof(f113,plain,
    ( spl14_1
  <=> r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f357,plain,
    ( spl14_29
  <=> sK2 = sK11(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_29])])).

fof(f420,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl14_1
    | ~ spl14_29 ),
    inference(forward_demodulation,[],[f416,f359])).

fof(f359,plain,
    ( sK2 = sK11(sK0,sK1,sK2)
    | ~ spl14_29 ),
    inference(avatar_component_clause,[],[f357])).

fof(f416,plain,
    ( sK0 = k1_relat_1(sK11(sK0,sK1,sK2))
    | ~ spl14_1 ),
    inference(resolution,[],[f105,f115])).

fof(f115,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | k1_relat_1(sK11(X0,X1,X3)) = X0 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relat_1(sK11(X0,X1,X3)) = X0
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f397,plain,
    ( spl14_34
    | ~ spl14_1
    | ~ spl14_29 ),
    inference(avatar_split_clause,[],[f392,f357,f113,f394])).

fof(f392,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl14_1
    | ~ spl14_29 ),
    inference(forward_demodulation,[],[f388,f359])).

fof(f388,plain,
    ( r1_tarski(k2_relat_1(sK11(sK0,sK1,sK2)),sK1)
    | ~ spl14_1 ),
    inference(resolution,[],[f104,f115])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK11(X0,X1,X3)),X1) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_relat_1(sK11(X0,X1,X3)),X1)
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f387,plain,
    ( spl14_33
    | ~ spl14_31
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f377,f126,f371,f384])).

fof(f377,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl14_4 ),
    inference(resolution,[],[f127,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f127,plain,
    ( v1_funct_1(sK2)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f382,plain,
    ( spl14_32
    | ~ spl14_31
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f376,f126,f371,f379])).

fof(f376,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl14_4 ),
    inference(resolution,[],[f127,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f375,plain,
    ( spl14_4
    | ~ spl14_23
    | ~ spl14_29 ),
    inference(avatar_split_clause,[],[f369,f357,f305,f126])).

fof(f305,plain,
    ( spl14_23
  <=> v1_funct_1(sK11(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).

fof(f369,plain,
    ( v1_funct_1(sK2)
    | ~ spl14_23
    | ~ spl14_29 ),
    inference(backward_demodulation,[],[f307,f359])).

fof(f307,plain,
    ( v1_funct_1(sK11(sK0,sK1,sK2))
    | ~ spl14_23 ),
    inference(avatar_component_clause,[],[f305])).

fof(f374,plain,
    ( spl14_31
    | ~ spl14_24
    | ~ spl14_29 ),
    inference(avatar_split_clause,[],[f368,f357,f318,f371])).

fof(f318,plain,
    ( spl14_24
  <=> v1_relat_1(sK11(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f368,plain,
    ( v1_relat_1(sK2)
    | ~ spl14_24
    | ~ spl14_29 ),
    inference(backward_demodulation,[],[f320,f359])).

fof(f320,plain,
    ( v1_relat_1(sK11(sK0,sK1,sK2))
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f318])).

fof(f360,plain,
    ( spl14_29
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f352,f113,f357])).

fof(f352,plain,
    ( sK2 = sK11(sK0,sK1,sK2)
    | ~ spl14_1 ),
    inference(resolution,[],[f106,f115])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | sK11(X0,X1,X3) = X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( sK11(X0,X1,X3) = X3
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f344,plain,
    ( spl14_26
    | ~ spl14_27
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f333,f318,f340,f336])).

fof(f336,plain,
    ( spl14_26
  <=> k1_xboole_0 = k1_relat_1(sK11(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f340,plain,
    ( spl14_27
  <=> k1_xboole_0 = k2_relat_1(sK11(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).

fof(f333,plain,
    ( k1_xboole_0 != k2_relat_1(sK11(sK0,sK1,sK2))
    | k1_xboole_0 = k1_relat_1(sK11(sK0,sK1,sK2))
    | ~ spl14_24 ),
    inference(resolution,[],[f320,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f321,plain,
    ( spl14_24
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f313,f113,f318])).

fof(f313,plain,
    ( v1_relat_1(sK11(sK0,sK1,sK2))
    | ~ spl14_1 ),
    inference(resolution,[],[f108,f115])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | v1_relat_1(sK11(X0,X1,X3)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_relat_1(sK11(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f308,plain,
    ( spl14_23
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f300,f113,f305])).

fof(f300,plain,
    ( v1_funct_1(sK11(sK0,sK1,sK2))
    | ~ spl14_1 ),
    inference(resolution,[],[f107,f115])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | v1_funct_1(sK11(X0,X1,X3)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK11(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f261,plain,
    ( spl14_18
    | ~ spl14_15 ),
    inference(avatar_split_clause,[],[f256,f222,f258])).

fof(f258,plain,
    ( spl14_18
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f222,plain,
    ( spl14_15
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f256,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl14_15 ),
    inference(superposition,[],[f46,f224])).

fof(f224,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f222])).

fof(f46,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f225,plain,
    ( spl14_15
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f219,f211,f222])).

fof(f211,plain,
    ( spl14_14
  <=> sP13(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f219,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl14_14 ),
    inference(resolution,[],[f213,f160])).

fof(f160,plain,(
    ! [X0] :
      ( ~ sP13(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f61,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP13(X1) ) ),
    inference(general_splitting,[],[f92,f110_D])).

fof(f110,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP13(X1) ) ),
    inference(cnf_transformation,[],[f110_D])).

fof(f110_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP13(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f213,plain,
    ( sP13(k6_partfun1(k1_xboole_0))
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f211])).

fof(f214,plain,
    ( spl14_14
    | ~ spl14_5
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f200,f155,f131,f211])).

fof(f131,plain,
    ( spl14_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f155,plain,
    ( spl14_8
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f200,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sP13(k6_partfun1(k1_xboole_0))
    | ~ spl14_8 ),
    inference(resolution,[],[f110,f157])).

fof(f157,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f159,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f153,f155])).

fof(f153,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f47,f100])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f134,plain,(
    spl14_5 ),
    inference(avatar_split_clause,[],[f45,f131])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f129,plain,
    ( ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f43,f126,f122,f118])).

fof(f43,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f116,plain,(
    spl14_1 ),
    inference(avatar_split_clause,[],[f44,f113])).

fof(f44,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:45:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (31836)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (31828)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (31824)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (31827)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (31822)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31820)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (31836)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (31842)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1206,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f116,f129,f134,f159,f214,f225,f261,f308,f321,f344,f360,f374,f375,f382,f387,f397,f425,f595,f735,f751,f756,f831,f1032,f1052,f1104,f1191,f1203])).
% 0.21/0.53  fof(f1203,plain,(
% 0.21/0.53    k1_xboole_0 != sK2 | sK2 != sK11(sK0,sK1,sK2) | sK0 != k1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK11(sK0,sK1,sK2)) | v1_partfun1(sK2,sK0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f1191,plain,(
% 0.21/0.53    spl14_36 | ~spl14_67),
% 0.21/0.53    inference(avatar_split_clause,[],[f1182,f748,f406])).
% 0.21/0.53  fof(f406,plain,(
% 0.21/0.53    spl14_36 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).
% 0.21/0.53  fof(f748,plain,(
% 0.21/0.53    spl14_67 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_67])])).
% 0.21/0.53  fof(f1182,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(sK2) | ~spl14_67),
% 0.21/0.53    inference(resolution,[],[f750,f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 0.21/0.53    inference(resolution,[],[f61,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f750,plain,(
% 0.21/0.53    v1_xboole_0(k2_relat_1(sK2)) | ~spl14_67),
% 0.21/0.53    inference(avatar_component_clause,[],[f748])).
% 0.21/0.53  fof(f1104,plain,(
% 0.21/0.53    spl14_75 | ~spl14_68),
% 0.21/0.53    inference(avatar_split_clause,[],[f1095,f753,f803])).
% 0.21/0.53  fof(f803,plain,(
% 0.21/0.53    spl14_75 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_75])])).
% 0.21/0.53  fof(f753,plain,(
% 0.21/0.53    spl14_68 <=> v1_xboole_0(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).
% 0.21/0.53  fof(f1095,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~spl14_68),
% 0.21/0.53    inference(resolution,[],[f755,f161])).
% 0.21/0.53  fof(f755,plain,(
% 0.21/0.53    v1_xboole_0(sK2) | ~spl14_68),
% 0.21/0.53    inference(avatar_component_clause,[],[f753])).
% 0.21/0.53  fof(f1052,plain,(
% 0.21/0.53    spl14_3 | ~spl14_66 | ~spl14_4 | ~spl14_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f1047,f118,f126,f744,f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    spl14_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 0.21/0.53  fof(f744,plain,(
% 0.21/0.53    spl14_66 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_66])])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl14_4 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl14_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.21/0.53  fof(f1047,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~v1_partfun1(sK2,sK0) | v1_funct_2(sK2,sK0,sK1) | ~spl14_2),
% 0.21/0.53    inference(resolution,[],[f119,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl14_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f1032,plain,(
% 0.21/0.53    ~spl14_31 | spl14_2 | ~spl14_34 | ~spl14_38),
% 0.21/0.53    inference(avatar_split_clause,[],[f1031,f422,f394,f118,f371])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    spl14_31 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_31])])).
% 0.21/0.53  fof(f394,plain,(
% 0.21/0.53    spl14_34 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).
% 0.21/0.53  fof(f422,plain,(
% 0.21/0.53    spl14_38 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).
% 0.21/0.53  fof(f1031,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_relat_1(sK2) | (~spl14_34 | ~spl14_38)),
% 0.21/0.53    inference(forward_demodulation,[],[f1028,f424])).
% 0.21/0.53  fof(f424,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK2) | ~spl14_38),
% 0.21/0.53    inference(avatar_component_clause,[],[f422])).
% 0.21/0.53  fof(f1028,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl14_34),
% 0.21/0.53    inference(resolution,[],[f512,f396])).
% 0.21/0.53  fof(f396,plain,(
% 0.21/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~spl14_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f394])).
% 0.21/0.53  fof(f512,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))) )),
% 0.21/0.53    inference(resolution,[],[f78,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.53  fof(f831,plain,(
% 0.21/0.53    sK2 != sK11(sK0,sK1,sK2) | k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK11(sK0,sK1,sK2))),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f756,plain,(
% 0.21/0.53    spl14_68 | ~spl14_67 | ~spl14_65),
% 0.21/0.53    inference(avatar_split_clause,[],[f739,f732,f748,f753])).
% 0.21/0.53  fof(f732,plain,(
% 0.21/0.53    spl14_65 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_65])])).
% 0.21/0.53  fof(f739,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_relat_1(sK2)) | v1_xboole_0(sK2) | ~spl14_65),
% 0.21/0.53    inference(resolution,[],[f734,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.53  fof(f734,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~spl14_65),
% 0.21/0.53    inference(avatar_component_clause,[],[f732])).
% 0.21/0.53  fof(f751,plain,(
% 0.21/0.53    spl14_66 | ~spl14_56 | ~spl14_4 | spl14_67 | ~spl14_65),
% 0.21/0.53    inference(avatar_split_clause,[],[f737,f732,f748,f126,f592,f744])).
% 0.21/0.53  fof(f592,plain,(
% 0.21/0.53    spl14_56 <=> v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_56])])).
% 0.21/0.53  fof(f737,plain,(
% 0.21/0.53    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | v1_partfun1(sK2,sK0) | ~spl14_65),
% 0.21/0.53    inference(resolution,[],[f734,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.53  fof(f735,plain,(
% 0.21/0.53    spl14_65 | ~spl14_32 | ~spl14_38),
% 0.21/0.53    inference(avatar_split_clause,[],[f730,f422,f379,f732])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    spl14_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).
% 0.21/0.53  % (31834)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  fof(f730,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | (~spl14_32 | ~spl14_38)),
% 0.21/0.53    inference(forward_demodulation,[],[f381,f424])).
% 0.21/0.53  fof(f381,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl14_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f379])).
% 0.21/0.53  fof(f595,plain,(
% 0.21/0.53    spl14_56 | ~spl14_33 | ~spl14_38),
% 0.21/0.53    inference(avatar_split_clause,[],[f590,f422,f384,f592])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    spl14_33 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_33])])).
% 0.21/0.53  fof(f590,plain,(
% 0.21/0.53    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | (~spl14_33 | ~spl14_38)),
% 0.21/0.53    inference(forward_demodulation,[],[f386,f424])).
% 0.21/0.53  fof(f386,plain,(
% 0.21/0.53    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl14_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f384])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    spl14_38 | ~spl14_1 | ~spl14_29),
% 0.21/0.53    inference(avatar_split_clause,[],[f420,f357,f113,f422])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl14_1 <=> r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.21/0.53  fof(f357,plain,(
% 0.21/0.53    spl14_29 <=> sK2 = sK11(sK0,sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl14_29])])).
% 0.21/0.53  fof(f420,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK2) | (~spl14_1 | ~spl14_29)),
% 0.21/0.53    inference(forward_demodulation,[],[f416,f359])).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    sK2 = sK11(sK0,sK1,sK2) | ~spl14_29),
% 0.21/0.53    inference(avatar_component_clause,[],[f357])).
% 0.21/0.53  fof(f416,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK11(sK0,sK1,sK2)) | ~spl14_1),
% 0.21/0.53    inference(resolution,[],[f105,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_funct_2(sK0,sK1)) | ~spl14_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | k1_relat_1(sK11(X0,X1,X3)) = X0) )),
% 0.21/0.53    inference(equality_resolution,[],[f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_relat_1(sK11(X0,X1,X3)) = X0 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 0.21/0.53  fof(f397,plain,(
% 0.21/0.53    spl14_34 | ~spl14_1 | ~spl14_29),
% 0.21/0.53    inference(avatar_split_clause,[],[f392,f357,f113,f394])).
% 0.21/0.53  fof(f392,plain,(
% 0.21/0.53    r1_tarski(k2_relat_1(sK2),sK1) | (~spl14_1 | ~spl14_29)),
% 0.21/0.53    inference(forward_demodulation,[],[f388,f359])).
% 0.21/0.53  fof(f388,plain,(
% 0.21/0.53    r1_tarski(k2_relat_1(sK11(sK0,sK1,sK2)),sK1) | ~spl14_1),
% 0.21/0.53    inference(resolution,[],[f104,f115])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | r1_tarski(k2_relat_1(sK11(X0,X1,X3)),X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_relat_1(sK11(X0,X1,X3)),X1) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    spl14_33 | ~spl14_31 | ~spl14_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f377,f126,f371,f384])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl14_4),
% 0.21/0.53    inference(resolution,[],[f127,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    v1_funct_1(sK2) | ~spl14_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f126])).
% 0.21/0.54  fof(f382,plain,(
% 0.21/0.54    spl14_32 | ~spl14_31 | ~spl14_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f376,f126,f371,f379])).
% 0.21/0.54  fof(f376,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl14_4),
% 0.21/0.54    inference(resolution,[],[f127,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f375,plain,(
% 0.21/0.54    spl14_4 | ~spl14_23 | ~spl14_29),
% 0.21/0.54    inference(avatar_split_clause,[],[f369,f357,f305,f126])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    spl14_23 <=> v1_funct_1(sK11(sK0,sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    v1_funct_1(sK2) | (~spl14_23 | ~spl14_29)),
% 0.21/0.54    inference(backward_demodulation,[],[f307,f359])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    v1_funct_1(sK11(sK0,sK1,sK2)) | ~spl14_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f305])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    spl14_31 | ~spl14_24 | ~spl14_29),
% 0.21/0.54    inference(avatar_split_clause,[],[f368,f357,f318,f371])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    spl14_24 <=> v1_relat_1(sK11(sK0,sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).
% 0.21/0.54  fof(f368,plain,(
% 0.21/0.54    v1_relat_1(sK2) | (~spl14_24 | ~spl14_29)),
% 0.21/0.54    inference(backward_demodulation,[],[f320,f359])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    v1_relat_1(sK11(sK0,sK1,sK2)) | ~spl14_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f318])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    spl14_29 | ~spl14_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f352,f113,f357])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    sK2 = sK11(sK0,sK1,sK2) | ~spl14_1),
% 0.21/0.54    inference(resolution,[],[f106,f115])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | sK11(X0,X1,X3) = X3) )),
% 0.21/0.54    inference(equality_resolution,[],[f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (sK11(X0,X1,X3) = X3 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f344,plain,(
% 0.21/0.54    spl14_26 | ~spl14_27 | ~spl14_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f333,f318,f340,f336])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    spl14_26 <=> k1_xboole_0 = k1_relat_1(sK11(sK0,sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    spl14_27 <=> k1_xboole_0 = k2_relat_1(sK11(sK0,sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    k1_xboole_0 != k2_relat_1(sK11(sK0,sK1,sK2)) | k1_xboole_0 = k1_relat_1(sK11(sK0,sK1,sK2)) | ~spl14_24),
% 0.21/0.54    inference(resolution,[],[f320,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    spl14_24 | ~spl14_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f313,f113,f318])).
% 0.21/0.54  fof(f313,plain,(
% 0.21/0.54    v1_relat_1(sK11(sK0,sK1,sK2)) | ~spl14_1),
% 0.21/0.54    inference(resolution,[],[f108,f115])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | v1_relat_1(sK11(X0,X1,X3))) )),
% 0.21/0.54    inference(equality_resolution,[],[f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (v1_relat_1(sK11(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    spl14_23 | ~spl14_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f300,f113,f305])).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    v1_funct_1(sK11(sK0,sK1,sK2)) | ~spl14_1),
% 0.21/0.54    inference(resolution,[],[f107,f115])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | v1_funct_1(sK11(X0,X1,X3))) )),
% 0.21/0.54    inference(equality_resolution,[],[f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK11(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    spl14_18 | ~spl14_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f256,f222,f258])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    spl14_18 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    spl14_15 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl14_15),
% 0.21/0.54    inference(superposition,[],[f46,f224])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl14_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f222])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,axiom,(
% 0.21/0.54    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    spl14_15 | ~spl14_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f219,f211,f222])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    spl14_14 <=> sP13(k6_partfun1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl14_14),
% 0.21/0.54    inference(resolution,[],[f213,f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X0] : (~sP13(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(resolution,[],[f61,f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP13(X1)) )),
% 0.21/0.54    inference(general_splitting,[],[f92,f110_D])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP13(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f110_D])).
% 0.21/0.54  fof(f110_D,plain,(
% 0.21/0.54    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP13(X1)) )),
% 0.21/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    sP13(k6_partfun1(k1_xboole_0)) | ~spl14_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f211])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    spl14_14 | ~spl14_5 | ~spl14_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f200,f155,f131,f211])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl14_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    spl14_8 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | sP13(k6_partfun1(k1_xboole_0)) | ~spl14_8),
% 0.21/0.54    inference(resolution,[],[f110,f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl14_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f155])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    spl14_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f153,f155])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    inference(superposition,[],[f47,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl14_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f131])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ~spl14_2 | ~spl14_3 | ~spl14_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f126,f122,f118])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(negated_conjecture,[],[f22])).
% 0.21/0.54  fof(f22,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl14_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f113])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (31836)------------------------------
% 0.21/0.54  % (31836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31836)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (31836)Memory used [KB]: 11513
% 0.21/0.54  % (31836)Time elapsed: 0.101 s
% 0.21/0.54  % (31836)------------------------------
% 0.21/0.54  % (31836)------------------------------
% 0.21/0.54  % (31825)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (31819)Success in time 0.176 s
%------------------------------------------------------------------------------
