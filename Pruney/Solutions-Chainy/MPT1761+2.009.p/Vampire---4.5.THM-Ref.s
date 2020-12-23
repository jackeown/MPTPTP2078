%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 249 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  422 (2295 expanded)
%              Number of equality atoms :   46 ( 156 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f488,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f71,f79,f244,f292,f386,f433,f467,f470,f482,f487])).

fof(f487,plain,(
    spl7_43 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl7_43 ),
    inference(resolution,[],[f432,f47])).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f432,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),k1_xboole_0)
    | spl7_43 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl7_43
  <=> r1_xboole_0(u1_struct_0(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f482,plain,(
    spl7_42 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl7_42 ),
    inference(resolution,[],[f429,f40])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tmap_1)).

fof(f429,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl7_42 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl7_42
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f470,plain,(
    spl7_41 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | spl7_41 ),
    inference(resolution,[],[f426,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f426,plain,
    ( ~ v2_pre_topc(sK0)
    | spl7_41 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl7_41
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f467,plain,(
    spl7_40 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl7_40 ),
    inference(resolution,[],[f423,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f423,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_40 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl7_40
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f433,plain,
    ( ~ spl7_36
    | ~ spl7_40
    | ~ spl7_41
    | ~ spl7_42
    | ~ spl7_43
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f420,f92,f431,f428,f425,f422,f373])).

fof(f373,plain,
    ( spl7_36
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f92,plain,
    ( spl7_4
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f420,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),k1_xboole_0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f404,f302])).

fof(f302,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f93,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f93,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f404,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f361,f38])).

fof(f38,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f361,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X1) ) ),
    inference(resolution,[],[f84,f60])).

fof(f60,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f54,f31])).

fof(f31,plain,(
    r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f51,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f386,plain,(
    spl7_36 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl7_36 ),
    inference(resolution,[],[f374,f36])).

fof(f36,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f374,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl7_36 ),
    inference(avatar_component_clause,[],[f373])).

fof(f292,plain,
    ( ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(trivial_inequality_removal,[],[f290])).

fof(f290,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK5)
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(superposition,[],[f289,f80])).

fof(f80,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)
    | ~ spl7_3 ),
    inference(resolution,[],[f78,f31])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_funct_1(k7_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X0) )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_3
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | k1_funct_1(k7_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f289,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5)
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f249,f264])).

fof(f264,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_subsumption,[],[f44,f45,f46,f36,f38,f256])).

fof(f256,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f128,f40])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,X1)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(global_subsumption,[],[f33,f41,f42,f43,f34,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f110,f83])).

fof(f83,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) ),
    inference(global_subsumption,[],[f33,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | k7_relat_1(sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) ) ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f34,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f249,plain,
    ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(sK4,sK5)
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f32,f248])).

fof(f248,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)
    | ~ spl7_5 ),
    inference(resolution,[],[f96,f30])).

fof(f30,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_5
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f32,plain,(
    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f244,plain,
    ( spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f243,f95,f92])).

fof(f243,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK3))
      | v1_xboole_0(u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2) = k1_funct_1(sK4,X2) ) ),
    inference(global_subsumption,[],[f193])).

fof(f193,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK3))
      | v1_xboole_0(u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2) = k1_funct_1(sK4,X2) ) ),
    inference(global_subsumption,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | v1_xboole_0(u1_struct_0(sK3))
      | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) ) ),
    inference(global_subsumption,[],[f33,f34,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(u1_struct_0(sK3))
      | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) ) ),
    inference(resolution,[],[f58,f35])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f79,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f74,f77,f64])).

fof(f64,plain,
    ( spl7_1
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(sK4)
      | k1_funct_1(k7_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X0) ) ),
    inference(resolution,[],[f57,f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f71,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl7_2 ),
    inference(resolution,[],[f68,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f68,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_2
  <=> v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f69,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f62,f67,f64])).

fof(f62,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (3915)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % (3915)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f488,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f69,f71,f79,f244,f292,f386,f433,f467,f470,f482,f487])).
% 0.20/0.46  fof(f487,plain,(
% 0.20/0.46    spl7_43),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f486])).
% 0.20/0.46  fof(f486,plain,(
% 0.20/0.46    $false | spl7_43),
% 0.20/0.46    inference(resolution,[],[f432,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.46  fof(f432,plain,(
% 0.20/0.46    ~r1_xboole_0(u1_struct_0(sK2),k1_xboole_0) | spl7_43),
% 0.20/0.46    inference(avatar_component_clause,[],[f431])).
% 0.20/0.46  fof(f431,plain,(
% 0.20/0.46    spl7_43 <=> r1_xboole_0(u1_struct_0(sK2),k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.20/0.46  fof(f482,plain,(
% 0.20/0.46    spl7_42),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f480])).
% 0.20/0.46  fof(f480,plain,(
% 0.20/0.46    $false | spl7_42),
% 0.20/0.46    inference(resolution,[],[f429,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    m1_pre_topc(sK2,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f12])).
% 0.20/0.46  fof(f12,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tmap_1)).
% 0.20/0.46  fof(f429,plain,(
% 0.20/0.46    ~m1_pre_topc(sK2,sK0) | spl7_42),
% 0.20/0.46    inference(avatar_component_clause,[],[f428])).
% 0.20/0.46  fof(f428,plain,(
% 0.20/0.46    spl7_42 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.20/0.46  fof(f470,plain,(
% 0.20/0.46    spl7_41),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f469])).
% 0.20/0.46  fof(f469,plain,(
% 0.20/0.46    $false | spl7_41),
% 0.20/0.46    inference(resolution,[],[f426,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    v2_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f426,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | spl7_41),
% 0.20/0.46    inference(avatar_component_clause,[],[f425])).
% 0.20/0.46  fof(f425,plain,(
% 0.20/0.46    spl7_41 <=> v2_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.20/0.46  fof(f467,plain,(
% 0.20/0.46    spl7_40),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f466])).
% 0.20/0.46  fof(f466,plain,(
% 0.20/0.46    $false | spl7_40),
% 0.20/0.46    inference(resolution,[],[f423,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f423,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | spl7_40),
% 0.20/0.46    inference(avatar_component_clause,[],[f422])).
% 0.20/0.46  fof(f422,plain,(
% 0.20/0.46    spl7_40 <=> l1_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.20/0.46  fof(f433,plain,(
% 0.20/0.46    ~spl7_36 | ~spl7_40 | ~spl7_41 | ~spl7_42 | ~spl7_43 | ~spl7_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f420,f92,f431,f428,f425,f422,f373])).
% 0.20/0.46  fof(f373,plain,(
% 0.20/0.46    spl7_36 <=> m1_pre_topc(sK2,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    spl7_4 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.46  fof(f420,plain,(
% 0.20/0.46    ~r1_xboole_0(u1_struct_0(sK2),k1_xboole_0) | ~m1_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK3) | ~spl7_4),
% 0.20/0.46    inference(forward_demodulation,[],[f404,f302])).
% 0.20/0.46  fof(f302,plain,(
% 0.20/0.46    k1_xboole_0 = u1_struct_0(sK3) | ~spl7_4),
% 0.20/0.46    inference(resolution,[],[f93,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    v1_xboole_0(u1_struct_0(sK3)) | ~spl7_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f92])).
% 0.20/0.46  fof(f404,plain,(
% 0.20/0.46    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK3)),
% 0.20/0.46    inference(resolution,[],[f361,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    m1_pre_topc(sK3,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f361,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(X1)) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X1)) )),
% 0.20/0.46    inference(resolution,[],[f84,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.46    inference(resolution,[],[f54,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    r2_hidden(sK5,u1_struct_0(sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v1_xboole_0(u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.20/0.46    inference(resolution,[],[f51,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.46    inference(flattening,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.46  fof(f386,plain,(
% 0.20/0.46    spl7_36),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f384])).
% 0.20/0.46  fof(f384,plain,(
% 0.20/0.46    $false | spl7_36),
% 0.20/0.46    inference(resolution,[],[f374,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    m1_pre_topc(sK2,sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f374,plain,(
% 0.20/0.46    ~m1_pre_topc(sK2,sK3) | spl7_36),
% 0.20/0.46    inference(avatar_component_clause,[],[f373])).
% 0.20/0.46  fof(f292,plain,(
% 0.20/0.46    ~spl7_3 | ~spl7_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f291])).
% 0.20/0.46  fof(f291,plain,(
% 0.20/0.46    $false | (~spl7_3 | ~spl7_5)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f290])).
% 0.20/0.46  fof(f290,plain,(
% 0.20/0.46    k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK5) | (~spl7_3 | ~spl7_5)),
% 0.20/0.46    inference(superposition,[],[f289,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) | ~spl7_3),
% 0.20/0.46    inference(resolution,[],[f78,f31])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k7_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X0)) ) | ~spl7_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f77])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    spl7_3 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | k1_funct_1(k7_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.46  fof(f289,plain,(
% 0.20/0.46    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5) | ~spl7_5),
% 0.20/0.46    inference(backward_demodulation,[],[f249,f264])).
% 0.20/0.46  fof(f264,plain,(
% 0.20/0.46    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.20/0.46    inference(global_subsumption,[],[f44,f45,f46,f36,f38,f256])).
% 0.20/0.46  fof(f256,plain,(
% 0.20/0.46    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK3) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(resolution,[],[f128,f40])).
% 0.20/0.46  fof(f128,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.46    inference(global_subsumption,[],[f33,f41,f42,f43,f34,f127])).
% 0.20/0.46  fof(f127,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f110,f83])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0)) )),
% 0.20/0.46    inference(global_subsumption,[],[f33,f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0)) )),
% 0.20/0.46    inference(resolution,[],[f59,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.46    inference(flattening,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.46    inference(resolution,[],[f50,f35])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    l1_pre_topc(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    v2_pre_topc(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~v2_struct_0(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    v1_funct_1(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ~v2_struct_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f249,plain,(
% 0.20/0.46    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(sK4,sK5) | ~spl7_5),
% 0.20/0.46    inference(backward_demodulation,[],[f32,f248])).
% 0.20/0.46  fof(f248,plain,(
% 0.20/0.46    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) | ~spl7_5),
% 0.20/0.46    inference(resolution,[],[f96,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0)) ) | ~spl7_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f95])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    spl7_5 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f244,plain,(
% 0.20/0.46    spl7_4 | spl7_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f243,f95,f92])).
% 0.20/0.46  fof(f243,plain,(
% 0.20/0.46    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2) = k1_funct_1(sK4,X2)) )),
% 0.20/0.46    inference(global_subsumption,[],[f193])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2) = k1_funct_1(sK4,X2)) )),
% 0.20/0.46    inference(global_subsumption,[],[f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0)) )),
% 0.20/0.47    inference(global_subsumption,[],[f33,f34,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK3)) | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0)) )),
% 0.20/0.47    inference(resolution,[],[f58,f35])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ~spl7_1 | spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f74,f77,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl7_1 <=> v1_relat_1(sK4)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(sK4) | k1_funct_1(k7_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.47    inference(resolution,[],[f57,f33])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl7_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    $false | spl7_2),
% 0.20/0.47    inference(resolution,[],[f68,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) | spl7_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl7_2 <=> v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl7_1 | ~spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f62,f67,f64])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) | v1_relat_1(sK4)),
% 0.20/0.47    inference(resolution,[],[f49,f35])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (3915)------------------------------
% 0.20/0.47  % (3915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3915)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (3915)Memory used [KB]: 11001
% 0.20/0.47  % (3915)Time elapsed: 0.032 s
% 0.20/0.47  % (3915)------------------------------
% 0.20/0.47  % (3915)------------------------------
% 0.20/0.47  % (3897)Success in time 0.117 s
%------------------------------------------------------------------------------
