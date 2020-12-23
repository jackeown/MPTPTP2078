%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 (1347 expanded)
%              Number of leaves         :   22 ( 483 expanded)
%              Depth                    :   18
%              Number of atoms          :  366 (8462 expanded)
%              Number of equality atoms :   96 (3262 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f211,f355])).

fof(f355,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f258,f346,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f346,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f345,f273])).

fof(f273,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f225,f267])).

fof(f267,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f110,f217,f260,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

% (28715)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f260,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f47,f228,f227,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f227,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f214,f83])).

fof(f83,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f214,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f96,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f92,f94])).

fof(f94,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f46,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

% (28708)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f49,f90])).

fof(f90,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f45,f57])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f228,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f215,f83])).

fof(f215,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f97,f88])).

fof(f97,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f91,f94])).

fof(f91,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f48,f90])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f217,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f107,f88])).

fof(f107,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f96,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f110,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f61,f96,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f225,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f193,f83])).

fof(f193,plain,(
    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(superposition,[],[f117,f141])).

fof(f141,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f110,f129,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f129,plain,(
    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f110,f108,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f108,plain,(
    v5_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f96,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f117,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f111,f55])).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f111,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f53,f110,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

% (28705)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f345,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK2,k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f342,f229])).

fof(f229,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f216,f83])).

fof(f216,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2,X0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f105,f88])).

fof(f105,plain,(
    ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f96,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f342,plain,
    ( ~ v1_xboole_0(k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f226,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f226,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f213,f83])).

fof(f213,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f95,f88])).

fof(f95,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f93,f94])).

fof(f93,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f51,f90])).

fof(f51,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f258,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f224,f255])).

fof(f255,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f251,f71])).

fof(f251,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f224,f58])).

fof(f224,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f142,f83])).

fof(f142,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f129,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f211,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f193,f206])).

fof(f206,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) != k1_relat_1(sK2)
    | spl3_1 ),
    inference(superposition,[],[f121,f124])).

fof(f124,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,X0)
    | spl3_1 ),
    inference(backward_demodulation,[],[f105,f118])).

fof(f118,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f110,f106,f107,f67])).

fof(f106,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f47,f84,f97,f96,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f121,plain,
    ( k1_relat_1(sK2) != k8_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(backward_demodulation,[],[f95,f118])).

fof(f89,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f50,f86,f82])).

fof(f50,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (28706)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.46  % (28704)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (28698)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (28712)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (28714)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (28701)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (28716)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (28700)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (28696)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (28697)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (28703)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (28699)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (28697)Refutation not found, incomplete strategy% (28697)------------------------------
% 0.20/0.49  % (28697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28707)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (28697)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28697)Memory used [KB]: 10618
% 0.20/0.50  % (28697)Time elapsed: 0.085 s
% 0.20/0.50  % (28697)------------------------------
% 0.20/0.50  % (28697)------------------------------
% 0.20/0.50  % (28713)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (28716)Refutation not found, incomplete strategy% (28716)------------------------------
% 0.20/0.50  % (28716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28716)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28716)Memory used [KB]: 10618
% 0.20/0.50  % (28716)Time elapsed: 0.094 s
% 0.20/0.50  % (28716)------------------------------
% 0.20/0.50  % (28716)------------------------------
% 0.20/0.50  % (28709)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (28711)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (28709)Refutation not found, incomplete strategy% (28709)------------------------------
% 0.20/0.50  % (28709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28709)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28709)Memory used [KB]: 1663
% 0.20/0.50  % (28709)Time elapsed: 0.099 s
% 0.20/0.50  % (28709)------------------------------
% 0.20/0.50  % (28709)------------------------------
% 0.20/0.50  % (28707)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f356,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f89,f211,f355])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f352])).
% 0.20/0.50  fof(f352,plain,(
% 0.20/0.50    $false | (~spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f258,f346,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.50  fof(f346,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | (~spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(forward_demodulation,[],[f345,f273])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | (~spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(backward_demodulation,[],[f225,f267])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | (~spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f110,f217,f260,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  % (28715)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    v1_partfun1(sK2,k1_xboole_0) | (~spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f47,f228,f227,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(equality_resolution,[],[f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(backward_demodulation,[],[f214,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl3_1 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | ~spl3_2),
% 0.20/0.51    inference(backward_demodulation,[],[f96,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.51    inference(backward_demodulation,[],[f92,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f46,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    l1_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f39,f38,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  % (28708)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.51    inference(backward_demodulation,[],[f49,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f45,f57])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    l1_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f228,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_1 | ~spl3_2)),
% 0.20/0.51    inference(backward_demodulation,[],[f215,f83])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) | ~spl3_2),
% 0.20/0.51    inference(backward_demodulation,[],[f97,f88])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.51    inference(backward_demodulation,[],[f91,f94])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.51    inference(backward_demodulation,[],[f48,f90])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    v4_relat_1(sK2,k1_xboole_0) | ~spl3_2),
% 0.20/0.51    inference(backward_demodulation,[],[f107,f88])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f96,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f61,f96,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0) | ~spl3_1),
% 0.20/0.51    inference(backward_demodulation,[],[f193,f83])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)),
% 0.20/0.51    inference(superposition,[],[f117,f141])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1)))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f110,f129,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f110,f108,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    v5_relat_1(sK2,k2_struct_0(sK1))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f96,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ( ! [X0] : (k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f111,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f53,f110,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  % (28705)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.51  fof(f345,plain,(
% 0.20/0.51    ~v1_xboole_0(k10_relat_1(sK2,k1_xboole_0)) | (~spl3_1 | ~spl3_2)),
% 0.20/0.51    inference(forward_demodulation,[],[f342,f229])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.51    inference(backward_demodulation,[],[f216,f83])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2,X0)) ) | ~spl3_2),
% 0.20/0.51    inference(backward_demodulation,[],[f105,f88])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f96,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.51  fof(f342,plain,(
% 0.20/0.51    ~v1_xboole_0(k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)) | (~spl3_1 | ~spl3_2)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f52,f226,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl3_1 | ~spl3_2)),
% 0.20/0.51    inference(backward_demodulation,[],[f213,f83])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    k1_xboole_0 != k8_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | ~spl3_2),
% 0.20/0.51    inference(backward_demodulation,[],[f95,f88])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.51    inference(backward_demodulation,[],[f93,f94])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.51    inference(backward_demodulation,[],[f51,f90])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f258,plain,(
% 0.20/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_1),
% 0.20/0.51    inference(backward_demodulation,[],[f224,f255])).
% 0.20/0.51  fof(f255,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f52,f251,f71])).
% 0.20/0.51  fof(f251,plain,(
% 0.20/0.51    v1_xboole_0(k2_relat_1(sK2)) | ~spl3_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f52,f224,f58])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl3_1),
% 0.20/0.51    inference(backward_demodulation,[],[f142,f83])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f129,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    spl3_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f207])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    $false | spl3_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f193,f206])).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    k10_relat_1(sK2,k2_struct_0(sK1)) != k1_relat_1(sK2) | spl3_1),
% 0.20/0.51    inference(superposition,[],[f121,f124])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,X0)) ) | spl3_1),
% 0.20/0.51    inference(backward_demodulation,[],[f105,f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | spl3_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f110,f106,f107,f67])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f47,f84,f97,f96,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    k1_xboole_0 != k2_struct_0(sK1) | spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    k1_relat_1(sK2) != k8_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.20/0.51    inference(backward_demodulation,[],[f95,f118])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ~spl3_1 | spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f86,f82])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (28707)------------------------------
% 0.20/0.51  % (28707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28707)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (28707)Memory used [KB]: 10746
% 0.20/0.51  % (28707)Time elapsed: 0.105 s
% 0.20/0.51  % (28707)------------------------------
% 0.20/0.51  % (28707)------------------------------
% 0.20/0.51  % (28693)Success in time 0.157 s
%------------------------------------------------------------------------------
