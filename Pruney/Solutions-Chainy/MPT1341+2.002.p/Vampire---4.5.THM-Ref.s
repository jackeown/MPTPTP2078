%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:35 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  146 (3358 expanded)
%              Number of leaves         :   18 ( 683 expanded)
%              Depth                    :   21
%              Number of atoms          :  446 (17366 expanded)
%              Number of equality atoms :  168 (5999 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f151,f221,f232,f283,f302,f374])).

fof(f374,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f131,f369])).

fof(f369,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f368,f108])).

fof(f108,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f38,f99,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f99,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f92,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f86,f89])).

fof(f89,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (12784)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f40,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f36,f82])).

fof(f82,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f39,f56])).

fof(f39,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f368,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f38,f34,f141,f336,f345,f346,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

% (12785)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f346,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f329,f216])).

fof(f216,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl3_8
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f329,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f91,f303])).

fof(f303,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f89,f152])).

% (12771)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f152,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f89,f146])).

fof(f146,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_3
  <=> k1_relat_1(sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f91,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f87,f89])).

fof(f87,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f37,f82])).

fof(f37,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f345,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f328,f216])).

fof(f328,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f92,f303])).

fof(f336,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f316,f216])).

fof(f316,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f137,f303])).

fof(f137,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_1
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f141,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f131,plain,(
    k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f129,f130])).

fof(f130,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f119,f108])).

fof(f119,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f34,f111,f92,f113,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f21])).

% (12782)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f113,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f34,f38,f93,f92,f91,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

% (12768)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f93,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f85,f89])).

fof(f85,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f35,f82])).

fof(f35,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f111,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f38,f93,f92,f91,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f129,plain,(
    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f116,f127])).

fof(f127,plain,(
    k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f121,f107])).

fof(f107,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f38,f99,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f121,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f92,f111,f113,f51])).

fof(f116,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f115,f114])).

fof(f114,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f38,f34,f93,f92,f91,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f115,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f103,f114])).

fof(f103,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) ),
    inference(backward_demodulation,[],[f95,f96])).

fof(f96,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f92,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f95,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2)
    | k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f94,f89])).

fof(f94,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) ),
    inference(backward_demodulation,[],[f88,f89])).

fof(f88,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK2)
    | k1_partfun1(u1_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f84,f82])).

fof(f84,plain,
    ( k1_partfun1(u1_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f70,f82])).

fof(f70,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f62,f37])).

fof(f62,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f43,f43])).

fof(f33,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f302,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f296])).

fof(f296,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f131,f212])).

fof(f212,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_7
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f283,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,
    ( k6_relat_1(k1_xboole_0) != k6_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f244,f276])).

fof(f276,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f245,f262])).

fof(f262,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f238,f239,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f239,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f113,f142])).

fof(f142,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f238,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f112,f142])).

fof(f112,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f38,f93,f92,f91,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f245,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f132,f142])).

fof(f132,plain,(
    k2_relat_1(sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f118,f105])).

fof(f105,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f38,f99,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f118,plain,(
    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f113,f50])).

fof(f244,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f131,f142])).

fof(f232,plain,
    ( ~ spl3_3
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl3_3
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f38,f34,f155,f154,f153,f220,f54])).

fof(f220,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl3_9
  <=> v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f153,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f91,f146])).

fof(f154,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f92,f146])).

fof(f155,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f93,f146])).

fof(f221,plain,
    ( spl3_7
    | spl3_8
    | ~ spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f166,f144,f218,f214,f210])).

fof(f166,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f165,f146])).

fof(f165,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f134,f146])).

fof(f134,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f126,f132])).

fof(f126,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f113,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f93,f138])).

fof(f138,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f136])).

fof(f147,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f104,f144,f140,f136])).

fof(f104,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f102,f96])).

fof(f102,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(resolution,[],[f92,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (12781)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (12772)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (12764)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.52  % (12763)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.52  % (12769)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.53  % (12765)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.53  % (12762)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.53  % (12760)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (12766)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.53  % (12770)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.54  % (12773)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.54  % (12787)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.24/0.54  % (12773)Refutation not found, incomplete strategy% (12773)------------------------------
% 1.24/0.54  % (12773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (12773)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (12773)Memory used [KB]: 6140
% 1.24/0.54  % (12773)Time elapsed: 0.002 s
% 1.24/0.54  % (12773)------------------------------
% 1.24/0.54  % (12773)------------------------------
% 1.24/0.54  % (12761)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (12788)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.54  % (12758)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (12777)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.54  % (12762)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f375,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(avatar_sat_refutation,[],[f147,f151,f221,f232,f283,f302,f374])).
% 1.37/0.54  fof(f374,plain,(
% 1.37/0.54    ~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_8),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f370])).
% 1.37/0.54  fof(f370,plain,(
% 1.37/0.54    $false | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_8)),
% 1.37/0.54    inference(unit_resulting_resolution,[],[f131,f369])).
% 1.37/0.54  fof(f369,plain,(
% 1.37/0.54    k6_relat_1(k2_struct_0(sK1)) = k6_relat_1(k2_relat_1(sK2)) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_8)),
% 1.37/0.54    inference(forward_demodulation,[],[f368,f108])).
% 1.37/0.54  fof(f108,plain,(
% 1.37/0.54    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 1.37/0.54    inference(unit_resulting_resolution,[],[f34,f38,f99,f58])).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f29])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.54    inference(flattening,[],[f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.37/0.54  fof(f99,plain,(
% 1.37/0.54    v1_relat_1(sK2)),
% 1.37/0.54    inference(unit_resulting_resolution,[],[f92,f61])).
% 1.37/0.54  fof(f61,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f32])).
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.54    inference(ennf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.37/0.54  fof(f92,plain,(
% 1.37/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.37/0.54    inference(backward_demodulation,[],[f86,f89])).
% 1.37/0.54  fof(f89,plain,(
% 1.37/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.37/0.54    inference(unit_resulting_resolution,[],[f40,f56])).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f27])).
% 1.37/0.55  % (12784)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.55  fof(f27,plain,(
% 1.37/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f10])).
% 1.37/0.55  fof(f10,axiom,(
% 1.37/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.37/0.55  fof(f40,plain,(
% 1.37/0.55    l1_struct_0(sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f15])).
% 1.37/0.55  fof(f15,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.37/0.55    inference(flattening,[],[f14])).
% 1.37/0.55  fof(f14,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : (? [X2] : (((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f13])).
% 1.37/0.55  fof(f13,negated_conjecture,(
% 1.37/0.55    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.37/0.55    inference(negated_conjecture,[],[f12])).
% 1.37/0.55  fof(f12,conjecture,(
% 1.37/0.55    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).
% 1.37/0.55  fof(f86,plain,(
% 1.37/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.37/0.55    inference(backward_demodulation,[],[f36,f82])).
% 1.37/0.55  fof(f82,plain,(
% 1.37/0.55    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f39,f56])).
% 1.37/0.55  fof(f39,plain,(
% 1.37/0.55    l1_struct_0(sK1)),
% 1.37/0.55    inference(cnf_transformation,[],[f15])).
% 1.37/0.55  fof(f36,plain,(
% 1.37/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.37/0.55    inference(cnf_transformation,[],[f15])).
% 1.37/0.55  fof(f38,plain,(
% 1.37/0.55    v2_funct_1(sK2)),
% 1.37/0.55    inference(cnf_transformation,[],[f15])).
% 1.37/0.55  fof(f34,plain,(
% 1.37/0.55    v1_funct_1(sK2)),
% 1.37/0.55    inference(cnf_transformation,[],[f15])).
% 1.37/0.55  fof(f368,plain,(
% 1.37/0.55    k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_8)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f38,f34,f141,f336,f345,f346,f63])).
% 1.37/0.55  fof(f63,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)) )),
% 1.37/0.55    inference(definition_unfolding,[],[f42,f43])).
% 1.37/0.55  fof(f43,plain,(
% 1.37/0.55    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f7])).
% 1.37/0.55  fof(f7,axiom,(
% 1.37/0.55    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.37/0.55  fof(f42,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f17])).
% 1.37/0.55  % (12785)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.55  fof(f17,plain,(
% 1.37/0.55    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.37/0.55    inference(flattening,[],[f16])).
% 1.37/0.55  fof(f16,plain,(
% 1.37/0.55    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.37/0.55    inference(ennf_transformation,[],[f9])).
% 1.37/0.55  fof(f9,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.37/0.55  fof(f346,plain,(
% 1.37/0.55    k2_struct_0(sK1) = k2_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_8)),
% 1.37/0.55    inference(backward_demodulation,[],[f329,f216])).
% 1.37/0.55  fof(f216,plain,(
% 1.37/0.55    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_8),
% 1.37/0.55    inference(avatar_component_clause,[],[f214])).
% 1.37/0.55  fof(f214,plain,(
% 1.37/0.55    spl3_8 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.37/0.55  fof(f329,plain,(
% 1.37/0.55    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~spl3_3),
% 1.37/0.55    inference(forward_demodulation,[],[f91,f303])).
% 1.37/0.55  fof(f303,plain,(
% 1.37/0.55    k1_relat_1(sK2) = k2_struct_0(sK0) | ~spl3_3),
% 1.37/0.55    inference(backward_demodulation,[],[f89,f152])).
% 1.37/0.55  % (12771)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.55  fof(f152,plain,(
% 1.37/0.55    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_3),
% 1.37/0.55    inference(backward_demodulation,[],[f89,f146])).
% 1.37/0.55  fof(f146,plain,(
% 1.37/0.55    k1_relat_1(sK2) = k2_struct_0(sK0) | ~spl3_3),
% 1.37/0.55    inference(avatar_component_clause,[],[f144])).
% 1.37/0.55  fof(f144,plain,(
% 1.37/0.55    spl3_3 <=> k1_relat_1(sK2) = k2_struct_0(sK0)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.37/0.55  fof(f91,plain,(
% 1.37/0.55    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.37/0.55    inference(backward_demodulation,[],[f87,f89])).
% 1.37/0.55  fof(f87,plain,(
% 1.37/0.55    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.37/0.55    inference(backward_demodulation,[],[f37,f82])).
% 1.37/0.55  fof(f37,plain,(
% 1.37/0.55    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.37/0.55    inference(cnf_transformation,[],[f15])).
% 1.37/0.55  fof(f345,plain,(
% 1.37/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | (~spl3_3 | ~spl3_8)),
% 1.37/0.55    inference(backward_demodulation,[],[f328,f216])).
% 1.37/0.55  fof(f328,plain,(
% 1.37/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~spl3_3),
% 1.37/0.55    inference(forward_demodulation,[],[f92,f303])).
% 1.37/0.55  fof(f336,plain,(
% 1.37/0.55    v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) | (~spl3_1 | ~spl3_3 | ~spl3_8)),
% 1.37/0.55    inference(backward_demodulation,[],[f316,f216])).
% 1.37/0.55  fof(f316,plain,(
% 1.37/0.55    v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | (~spl3_1 | ~spl3_3)),
% 1.37/0.55    inference(forward_demodulation,[],[f137,f303])).
% 1.37/0.55  fof(f137,plain,(
% 1.37/0.55    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_1),
% 1.37/0.55    inference(avatar_component_clause,[],[f136])).
% 1.37/0.55  fof(f136,plain,(
% 1.37/0.55    spl3_1 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.37/0.55  fof(f141,plain,(
% 1.37/0.55    k1_xboole_0 != k2_struct_0(sK1) | spl3_2),
% 1.37/0.55    inference(avatar_component_clause,[],[f140])).
% 1.37/0.55  fof(f140,plain,(
% 1.37/0.55    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.37/0.55  fof(f131,plain,(
% 1.37/0.55    k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(sK2))),
% 1.37/0.55    inference(backward_demodulation,[],[f129,f130])).
% 1.37/0.55  fof(f130,plain,(
% 1.37/0.55    k6_relat_1(k2_relat_1(sK2)) = k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)),
% 1.37/0.55    inference(forward_demodulation,[],[f119,f108])).
% 1.37/0.56  fof(f119,plain,(
% 1.37/0.56    k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f34,f111,f92,f113,f51])).
% 1.37/0.56  fof(f51,plain,(
% 1.37/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f22])).
% 1.37/0.56  fof(f22,plain,(
% 1.37/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.37/0.56    inference(flattening,[],[f21])).
% 1.37/0.56  % (12782)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.56  fof(f21,plain,(
% 1.37/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.37/0.56    inference(ennf_transformation,[],[f6])).
% 1.37/0.56  fof(f6,axiom,(
% 1.37/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.37/0.56  fof(f113,plain,(
% 1.37/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f34,f38,f93,f92,f91,f55])).
% 1.37/0.56  fof(f55,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f26])).
% 1.37/0.56  fof(f26,plain,(
% 1.37/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.37/0.56    inference(flattening,[],[f25])).
% 1.37/0.56  fof(f25,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.37/0.56    inference(ennf_transformation,[],[f8])).
% 1.37/0.56  fof(f8,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.37/0.56  % (12768)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.56  fof(f93,plain,(
% 1.37/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.37/0.56    inference(backward_demodulation,[],[f85,f89])).
% 1.37/0.56  fof(f85,plain,(
% 1.37/0.56    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 1.37/0.56    inference(backward_demodulation,[],[f35,f82])).
% 1.37/0.56  fof(f35,plain,(
% 1.37/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.37/0.56    inference(cnf_transformation,[],[f15])).
% 1.37/0.56  fof(f111,plain,(
% 1.37/0.56    v1_funct_1(k2_funct_1(sK2))),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f34,f38,f93,f92,f91,f53])).
% 1.37/0.56  fof(f53,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f26])).
% 1.37/0.56  fof(f129,plain,(
% 1.37/0.56    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f128])).
% 1.37/0.56  fof(f128,plain,(
% 1.37/0.56    k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)),
% 1.37/0.56    inference(backward_demodulation,[],[f116,f127])).
% 1.37/0.56  fof(f127,plain,(
% 1.37/0.56    k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))),
% 1.37/0.56    inference(forward_demodulation,[],[f121,f107])).
% 1.37/0.56  fof(f107,plain,(
% 1.37/0.56    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f34,f38,f99,f57])).
% 1.37/0.56  fof(f57,plain,(
% 1.37/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f29])).
% 1.37/0.56  fof(f121,plain,(
% 1.37/0.56    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f34,f92,f111,f113,f51])).
% 1.37/0.56  fof(f116,plain,(
% 1.37/0.56    k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)),
% 1.37/0.56    inference(forward_demodulation,[],[f115,f114])).
% 1.37/0.56  fof(f114,plain,(
% 1.37/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f38,f34,f93,f92,f91,f52])).
% 1.37/0.56  fof(f52,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f24])).
% 1.37/0.56  fof(f24,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.37/0.56    inference(flattening,[],[f23])).
% 1.37/0.56  fof(f23,plain,(
% 1.37/0.56    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.37/0.56    inference(ennf_transformation,[],[f11])).
% 1.37/0.56  fof(f11,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.37/0.56  fof(f115,plain,(
% 1.37/0.56    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.37/0.56    inference(backward_demodulation,[],[f103,f114])).
% 1.37/0.56  fof(f103,plain,(
% 1.37/0.56    k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2)),
% 1.37/0.56    inference(backward_demodulation,[],[f95,f96])).
% 1.37/0.56  fof(f96,plain,(
% 1.37/0.56    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f92,f50])).
% 1.37/0.56  fof(f50,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f20])).
% 1.37/0.56  fof(f20,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.56    inference(ennf_transformation,[],[f4])).
% 1.37/0.56  fof(f4,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.37/0.56  fof(f95,plain,(
% 1.37/0.56    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) | k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.37/0.56    inference(forward_demodulation,[],[f94,f89])).
% 1.37/0.56  fof(f94,plain,(
% 1.37/0.56    k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK2)),
% 1.37/0.56    inference(backward_demodulation,[],[f88,f89])).
% 1.37/0.56  fof(f88,plain,(
% 1.37/0.56    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) | k1_partfun1(u1_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.37/0.56    inference(forward_demodulation,[],[f84,f82])).
% 1.37/0.56  fof(f84,plain,(
% 1.37/0.56    k1_partfun1(u1_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1))),
% 1.37/0.56    inference(backward_demodulation,[],[f70,f82])).
% 1.37/0.56  fof(f70,plain,(
% 1.37/0.56    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.37/0.56    inference(forward_demodulation,[],[f62,f37])).
% 1.37/0.56  fof(f62,plain,(
% 1.37/0.56    k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.37/0.56    inference(definition_unfolding,[],[f33,f43,f43])).
% 1.37/0.56  fof(f33,plain,(
% 1.37/0.56    k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.37/0.56    inference(cnf_transformation,[],[f15])).
% 1.37/0.56  fof(f302,plain,(
% 1.37/0.56    ~spl3_7),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f301])).
% 1.37/0.56  fof(f301,plain,(
% 1.37/0.56    $false | ~spl3_7),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f296])).
% 1.37/0.56  fof(f296,plain,(
% 1.37/0.56    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k2_relat_1(sK2)) | ~spl3_7),
% 1.37/0.56    inference(backward_demodulation,[],[f131,f212])).
% 1.37/0.56  fof(f212,plain,(
% 1.37/0.56    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_7),
% 1.37/0.56    inference(avatar_component_clause,[],[f210])).
% 1.37/0.56  fof(f210,plain,(
% 1.37/0.56    spl3_7 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.37/0.56  fof(f283,plain,(
% 1.37/0.56    ~spl3_2),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f282])).
% 1.37/0.56  fof(f282,plain,(
% 1.37/0.56    $false | ~spl3_2),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f281])).
% 1.37/0.56  fof(f281,plain,(
% 1.37/0.56    k6_relat_1(k1_xboole_0) != k6_relat_1(k1_xboole_0) | ~spl3_2),
% 1.37/0.56    inference(backward_demodulation,[],[f244,f276])).
% 1.37/0.56  fof(f276,plain,(
% 1.37/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_2),
% 1.37/0.56    inference(backward_demodulation,[],[f245,f262])).
% 1.37/0.56  fof(f262,plain,(
% 1.37/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_2),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f238,f239,f65])).
% 1.37/0.56  fof(f65,plain,(
% 1.37/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.37/0.56    inference(equality_resolution,[],[f47])).
% 1.37/0.56  fof(f47,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f19])).
% 1.37/0.56  fof(f19,plain,(
% 1.37/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.56    inference(flattening,[],[f18])).
% 1.37/0.56  fof(f18,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.56    inference(ennf_transformation,[],[f5])).
% 1.37/0.56  fof(f5,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.37/0.56  fof(f239,plain,(
% 1.37/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~spl3_2),
% 1.37/0.56    inference(backward_demodulation,[],[f113,f142])).
% 1.37/0.56  fof(f142,plain,(
% 1.37/0.56    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_2),
% 1.37/0.56    inference(avatar_component_clause,[],[f140])).
% 1.37/0.56  fof(f238,plain,(
% 1.37/0.56    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~spl3_2),
% 1.37/0.56    inference(backward_demodulation,[],[f112,f142])).
% 1.37/0.56  fof(f112,plain,(
% 1.37/0.56    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f34,f38,f93,f92,f91,f54])).
% 1.37/0.56  fof(f54,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f26])).
% 1.37/0.56  fof(f245,plain,(
% 1.37/0.56    k2_relat_1(sK2) = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_2),
% 1.37/0.56    inference(backward_demodulation,[],[f132,f142])).
% 1.37/0.56  fof(f132,plain,(
% 1.37/0.56    k2_relat_1(sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.37/0.56    inference(forward_demodulation,[],[f118,f105])).
% 1.37/0.56  fof(f105,plain,(
% 1.37/0.56    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f34,f38,f99,f59])).
% 1.37/0.56  fof(f59,plain,(
% 1.37/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f31])).
% 1.37/0.56  fof(f31,plain,(
% 1.37/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.56    inference(flattening,[],[f30])).
% 1.37/0.56  fof(f30,plain,(
% 1.37/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.56    inference(ennf_transformation,[],[f1])).
% 1.37/0.56  fof(f1,axiom,(
% 1.37/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.37/0.56  fof(f118,plain,(
% 1.37/0.56    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f113,f50])).
% 1.37/0.56  fof(f244,plain,(
% 1.37/0.56    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_xboole_0) | ~spl3_2),
% 1.37/0.56    inference(backward_demodulation,[],[f131,f142])).
% 1.37/0.56  fof(f232,plain,(
% 1.37/0.56    ~spl3_3 | spl3_9),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f228])).
% 1.37/0.56  fof(f228,plain,(
% 1.37/0.56    $false | (~spl3_3 | spl3_9)),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f38,f34,f155,f154,f153,f220,f54])).
% 1.37/0.56  fof(f220,plain,(
% 1.37/0.56    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | spl3_9),
% 1.37/0.56    inference(avatar_component_clause,[],[f218])).
% 1.37/0.56  fof(f218,plain,(
% 1.37/0.56    spl3_9 <=> v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.37/0.56  fof(f153,plain,(
% 1.37/0.56    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~spl3_3),
% 1.37/0.56    inference(backward_demodulation,[],[f91,f146])).
% 1.37/0.56  fof(f154,plain,(
% 1.37/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~spl3_3),
% 1.37/0.56    inference(backward_demodulation,[],[f92,f146])).
% 1.37/0.56  fof(f155,plain,(
% 1.37/0.56    v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~spl3_3),
% 1.37/0.56    inference(backward_demodulation,[],[f93,f146])).
% 1.37/0.56  fof(f221,plain,(
% 1.37/0.56    spl3_7 | spl3_8 | ~spl3_9 | ~spl3_3),
% 1.37/0.56    inference(avatar_split_clause,[],[f166,f144,f218,f214,f210])).
% 1.37/0.56  fof(f166,plain,(
% 1.37/0.56    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_3),
% 1.37/0.56    inference(forward_demodulation,[],[f165,f146])).
% 1.37/0.56  fof(f165,plain,(
% 1.37/0.56    k1_xboole_0 = k1_relat_1(sK2) | k2_struct_0(sK1) = k2_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~spl3_3),
% 1.37/0.56    inference(backward_demodulation,[],[f134,f146])).
% 1.37/0.56  fof(f134,plain,(
% 1.37/0.56    k2_struct_0(sK1) = k2_relat_1(sK2) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.37/0.56    inference(forward_demodulation,[],[f126,f132])).
% 1.37/0.56  fof(f126,plain,(
% 1.37/0.56    k1_xboole_0 = k2_struct_0(sK0) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.37/0.56    inference(resolution,[],[f113,f49])).
% 1.37/0.56  fof(f49,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f19])).
% 1.37/0.56  fof(f151,plain,(
% 1.37/0.56    spl3_1),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f148])).
% 1.37/0.56  fof(f148,plain,(
% 1.37/0.56    $false | spl3_1),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f93,f138])).
% 1.37/0.56  fof(f138,plain,(
% 1.37/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | spl3_1),
% 1.37/0.56    inference(avatar_component_clause,[],[f136])).
% 1.37/0.56  fof(f147,plain,(
% 1.37/0.56    ~spl3_1 | spl3_2 | spl3_3),
% 1.37/0.56    inference(avatar_split_clause,[],[f104,f144,f140,f136])).
% 1.37/0.56  fof(f104,plain,(
% 1.37/0.56    k1_relat_1(sK2) = k2_struct_0(sK0) | k1_xboole_0 = k2_struct_0(sK1) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.37/0.56    inference(forward_demodulation,[],[f102,f96])).
% 1.37/0.56  fof(f102,plain,(
% 1.37/0.56    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.37/0.56    inference(resolution,[],[f92,f49])).
% 1.37/0.56  % SZS output end Proof for theBenchmark
% 1.37/0.56  % (12762)------------------------------
% 1.37/0.56  % (12762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (12762)Termination reason: Refutation
% 1.37/0.56  
% 1.37/0.56  % (12762)Memory used [KB]: 6396
% 1.37/0.56  % (12762)Time elapsed: 0.120 s
% 1.37/0.56  % (12762)------------------------------
% 1.37/0.56  % (12762)------------------------------
% 1.37/0.56  % (12753)Success in time 0.193 s
%------------------------------------------------------------------------------
