%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 967 expanded)
%              Number of leaves         :   22 ( 176 expanded)
%              Depth                    :   32
%              Number of atoms          :  657 (7708 expanded)
%              Number of equality atoms :   69 ( 660 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f848,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f519,f731,f736,f847])).

fof(f847,plain,
    ( ~ spl4_5
    | spl4_37
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f846])).

fof(f846,plain,
    ( $false
    | ~ spl4_5
    | spl4_37
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f845,f740])).

fof(f740,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | spl4_37
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f739,f50])).

fof(f50,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

fof(f739,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_37
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f737,f726])).

fof(f726,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl4_37
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f737,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_38 ),
    inference(resolution,[],[f730,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f730,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | r1_funct_2(X1,X0,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
        | v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,X1,X0) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f729])).

fof(f729,plain,
    ( spl4_38
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r1_funct_2(X1,X0,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f845,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f520,f844])).

fof(f844,plain,
    ( sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f843,f131])).

fof(f131,plain,(
    sK3 = k7_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f129,f114])).

fof(f114,plain,(
    v4_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f81,f51])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f129,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f74,f99])).

fof(f99,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f80,f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f843,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f841,f141])).

fof(f141,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_5
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f841,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f837,f55])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f837,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) ) ),
    inference(forward_demodulation,[],[f836,f262])).

fof(f262,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) ),
    inference(resolution,[],[f261,f51])).

fof(f261,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f836,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f835,f51])).

fof(f835,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f834,f49])).

fof(f834,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f833,f50])).

fof(f833,plain,(
    ! [X10,X9] :
      ( ~ v1_funct_2(X9,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,X9,X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X9,u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f832,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f832,plain,(
    ! [X10,X9] :
      ( v2_struct_0(sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,X9,X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X9,u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f829,f58])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f829,plain,(
    ! [X10,X9] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,X9,X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X9,u1_struct_0(X10)) ) ),
    inference(resolution,[],[f822,f57])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f822,plain,(
    ! [X12,X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(X10),u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,X10)
      | k2_tmap_1(X10,sK0,X11,X12) = k2_partfun1(u1_struct_0(X10),u1_struct_0(sK0),X11,u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f821,f61])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f821,plain,(
    ! [X12,X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(X10),u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,X10)
      | k2_tmap_1(X10,sK0,X11,X12) = k2_partfun1(u1_struct_0(X10),u1_struct_0(sK0),X11,u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f819,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f819,plain,(
    ! [X12,X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(sK0)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(X10),u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,X10)
      | k2_tmap_1(X10,sK0,X11,X12) = k2_partfun1(u1_struct_0(X10),u1_struct_0(sK0),X11,u1_struct_0(X12)) ) ),
    inference(resolution,[],[f69,f60])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f520,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f53,f141])).

fof(f53,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f736,plain,(
    ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f735])).

fof(f735,plain,
    ( $false
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f734,f61])).

fof(f734,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_37 ),
    inference(resolution,[],[f733,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f733,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f732,f59])).

fof(f732,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_37 ),
    inference(resolution,[],[f727,f68])).

% (1334)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f727,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f725])).

fof(f731,plain,
    ( spl4_37
    | spl4_38 ),
    inference(avatar_split_clause,[],[f723,f729,f725])).

fof(f723,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_2(sK3,X1,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(u1_struct_0(sK0))
      | r1_funct_2(X1,X0,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) ) ),
    inference(subsumption_resolution,[],[f721,f50])).

fof(f721,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_2(sK3,X1,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | r1_funct_2(X1,X0,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) ) ),
    inference(resolution,[],[f720,f51])).

fof(f720,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(sK3,X2,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(sK3,X3,X0)
      | v1_xboole_0(X0)
      | r1_funct_2(X2,X1,X3,X0,sK3,sK3) ) ),
    inference(resolution,[],[f90,f49])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 != X5
      | r1_funct_2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f519,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f517,f145])).

fof(f145,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_6
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f517,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f510,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f510,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f505,f134])).

fof(f134,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f64,f95])).

fof(f95,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f93,f55])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f63,f58])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f505,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(subsumption_resolution,[],[f495,f95])).

fof(f495,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f483,f340])).

fof(f340,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(k1_tsep_1(sK1,sK1,sK1),X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(backward_demodulation,[],[f300,f329])).

fof(f329,plain,(
    k1_tsep_1(sK1,sK2,sK2) = k1_tsep_1(sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f286,f328])).

fof(f328,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f284,f56])).

fof(f284,plain,
    ( v2_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK1,sK1) ),
    inference(resolution,[],[f278,f219])).

fof(f219,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f215,f58])).

fof(f215,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f213,f153])).

fof(f153,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f152,f55])).

fof(f152,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | ~ m1_pre_topc(sK2,sK1) ),
    inference(superposition,[],[f147,f52])).

fof(f52,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f147,plain,(
    ! [X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f65,f58])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f213,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f210,f58])).

fof(f210,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) ) ),
    inference(resolution,[],[f92,f57])).

fof(f92,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(subsumption_resolution,[],[f91,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(subsumption_resolution,[],[f85,f63])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f278,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK1,X0,X0) ) ),
    inference(subsumption_resolution,[],[f277,f58])).

fof(f277,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK1,X0,X0) ) ),
    inference(subsumption_resolution,[],[f274,f56])).

fof(f274,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK1,X0,X0) ) ),
    inference(resolution,[],[f70,f57])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f286,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK2,sK2) ),
    inference(backward_demodulation,[],[f52,f285])).

fof(f285,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK2,sK2) ),
    inference(subsumption_resolution,[],[f281,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f281,plain,
    ( v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK2,sK2) ),
    inference(resolution,[],[f278,f55])).

fof(f300,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK2),X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(backward_demodulation,[],[f213,f286])).

fof(f483,plain,(
    m1_pre_topc(k1_tsep_1(sK1,sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f374,f480])).

fof(f480,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f479,f56])).

fof(f479,plain,
    ( v2_struct_0(sK1)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f478,f55])).

fof(f478,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f477,f54])).

% (1330)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f477,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f476,f58])).

fof(f476,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f475,f57])).

fof(f475,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | m1_pre_topc(sK2,sK2) ),
    inference(trivial_inequality_removal,[],[f474])).

fof(f474,plain,
    ( k1_tsep_1(sK1,sK1,sK1) != k1_tsep_1(sK1,sK1,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | m1_pre_topc(sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f473])).

fof(f473,plain,
    ( k1_tsep_1(sK1,sK1,sK1) != k1_tsep_1(sK1,sK1,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | m1_pre_topc(sK2,sK2) ),
    inference(superposition,[],[f470,f329])).

fof(f470,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(sK1,sK1,sK1) != k1_tsep_1(X0,X1,sK2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f468,f54])).

fof(f468,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(sK1,sK1,sK1) != k1_tsep_1(X0,X1,sK2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(X1,sK2) ) ),
    inference(superposition,[],[f71,f330])).

fof(f330,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f285,f329])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f374,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK1,sK1),sK2)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(superposition,[],[f149,f330])).

% (1349)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f149,plain,(
    ! [X2] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),sK2)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f65,f95])).

fof(f146,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f137,f143,f139])).

fof(f137,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(resolution,[],[f136,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f136,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f135,f79])).

fof(f135,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f132,f55])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f64,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (1338)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (1346)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (1332)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (1348)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (1332)Refutation not found, incomplete strategy% (1332)------------------------------
% 0.21/0.51  % (1332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1327)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (1337)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (1332)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1332)Memory used [KB]: 10618
% 0.21/0.51  % (1332)Time elapsed: 0.075 s
% 0.21/0.51  % (1332)------------------------------
% 0.21/0.51  % (1332)------------------------------
% 0.21/0.52  % (1342)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (1336)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (1341)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (1348)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f848,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f146,f519,f731,f736,f847])).
% 0.21/0.52  fof(f847,plain,(
% 0.21/0.52    ~spl4_5 | spl4_37 | ~spl4_38),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f846])).
% 0.21/0.52  fof(f846,plain,(
% 0.21/0.52    $false | (~spl4_5 | spl4_37 | ~spl4_38)),
% 0.21/0.52    inference(subsumption_resolution,[],[f845,f740])).
% 0.21/0.52  fof(f740,plain,(
% 0.21/0.52    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | (spl4_37 | ~spl4_38)),
% 0.21/0.52    inference(subsumption_resolution,[],[f739,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f18])).
% 0.21/0.52  fof(f18,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).
% 0.21/0.52  fof(f739,plain,(
% 0.21/0.52    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | (spl4_37 | ~spl4_38)),
% 0.21/0.52    inference(subsumption_resolution,[],[f737,f726])).
% 0.21/0.52  fof(f726,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f725])).
% 0.21/0.52  fof(f725,plain,(
% 0.21/0.52    spl4_37 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.52  fof(f737,plain,(
% 0.21/0.52    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_38),
% 0.21/0.52    inference(resolution,[],[f730,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f730,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | r1_funct_2(X1,X0,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | v1_xboole_0(X0) | ~v1_funct_2(sK3,X1,X0)) ) | ~spl4_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f729])).
% 0.21/0.52  fof(f729,plain,(
% 0.21/0.52    spl4_38 <=> ! [X1,X0] : (v1_xboole_0(X0) | r1_funct_2(X1,X0,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.52  fof(f845,plain,(
% 0.21/0.52    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | ~spl4_5),
% 0.21/0.52    inference(backward_demodulation,[],[f520,f844])).
% 0.21/0.52  fof(f844,plain,(
% 0.21/0.52    sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) | ~spl4_5),
% 0.21/0.52    inference(forward_demodulation,[],[f843,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    sK3 = k7_relat_1(sK3,u1_struct_0(sK1))),
% 0.21/0.52    inference(resolution,[],[f129,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    v4_relat_1(sK3,u1_struct_0(sK1))),
% 0.21/0.52    inference(resolution,[],[f81,f51])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) )),
% 0.21/0.52    inference(resolution,[],[f74,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    v1_relat_1(sK3)),
% 0.21/0.52    inference(resolution,[],[f80,f51])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f843,plain,(
% 0.21/0.52    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK1)) | ~spl4_5),
% 0.21/0.52    inference(forward_demodulation,[],[f841,f141])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl4_5 <=> u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f841,plain,(
% 0.21/0.52    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.21/0.52    inference(resolution,[],[f837,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f837,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f836,f262])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0)) )),
% 0.21/0.52    inference(resolution,[],[f261,f51])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) )),
% 0.21/0.52    inference(resolution,[],[f82,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.52  fof(f836,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f835,f51])).
% 0.21/0.52  fof(f835,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f834,f49])).
% 0.21/0.52  fof(f834,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.21/0.52    inference(resolution,[],[f833,f50])).
% 0.21/0.52  fof(f833,plain,(
% 0.21/0.52    ( ! [X10,X9] : (~v1_funct_2(X9,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,X9,X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X9,u1_struct_0(X10))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f832,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~v2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f832,plain,(
% 0.21/0.52    ( ! [X10,X9] : (v2_struct_0(sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,X9,X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X9,u1_struct_0(X10))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f829,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f829,plain,(
% 0.21/0.52    ( ! [X10,X9] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,X9,X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X9,u1_struct_0(X10))) )),
% 0.21/0.52    inference(resolution,[],[f822,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    v2_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f822,plain,(
% 0.21/0.52    ( ! [X12,X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(X10) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(X10),u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,X10) | k2_tmap_1(X10,sK0,X11,X12) = k2_partfun1(u1_struct_0(X10),u1_struct_0(sK0),X11,u1_struct_0(X12))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f821,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f821,plain,(
% 0.21/0.52    ( ! [X12,X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(X10) | ~l1_pre_topc(sK0) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(X10),u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,X10) | k2_tmap_1(X10,sK0,X11,X12) = k2_partfun1(u1_struct_0(X10),u1_struct_0(sK0),X11,u1_struct_0(X12))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f819,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f819,plain,(
% 0.21/0.52    ( ! [X12,X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(sK0) | v2_struct_0(X10) | ~l1_pre_topc(sK0) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(X10),u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,X10) | k2_tmap_1(X10,sK0,X11,X12) = k2_partfun1(u1_struct_0(X10),u1_struct_0(sK0),X11,u1_struct_0(X12))) )),
% 0.21/0.52    inference(resolution,[],[f69,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.52  fof(f520,plain,(
% 0.21/0.52    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | ~spl4_5),
% 0.21/0.52    inference(backward_demodulation,[],[f53,f141])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f736,plain,(
% 0.21/0.52    ~spl4_37),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f735])).
% 0.21/0.52  fof(f735,plain,(
% 0.21/0.52    $false | ~spl4_37),
% 0.21/0.52    inference(subsumption_resolution,[],[f734,f61])).
% 0.21/0.52  fof(f734,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~spl4_37),
% 0.21/0.52    inference(resolution,[],[f733,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f733,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | ~spl4_37),
% 0.21/0.52    inference(subsumption_resolution,[],[f732,f59])).
% 0.21/0.52  fof(f732,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_37),
% 0.21/0.52    inference(resolution,[],[f727,f68])).
% 0.21/0.52  % (1334)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f727,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_37),
% 0.21/0.53    inference(avatar_component_clause,[],[f725])).
% 0.21/0.53  fof(f731,plain,(
% 0.21/0.53    spl4_37 | spl4_38),
% 0.21/0.53    inference(avatar_split_clause,[],[f723,f729,f725])).
% 0.21/0.53  fof(f723,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(sK3,X1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(u1_struct_0(sK0)) | r1_funct_2(X1,X0,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f721,f50])).
% 0.21/0.53  fof(f721,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(sK3,X1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | r1_funct_2(X1,X0,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)) )),
% 0.21/0.53    inference(resolution,[],[f720,f51])).
% 0.21/0.53  fof(f720,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | v1_xboole_0(X1) | ~v1_funct_2(sK3,X2,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(sK3,X3,X0) | v1_xboole_0(X0) | r1_funct_2(X2,X1,X3,X0,sK3,sK3)) )),
% 0.21/0.53    inference(resolution,[],[f90,f49])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5)) )),
% 0.21/0.53    inference(equality_resolution,[],[f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 != X5 | r1_funct_2(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.21/0.53    inference(flattening,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.21/0.53  fof(f519,plain,(
% 0.21/0.53    spl4_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f518])).
% 0.21/0.53  fof(f518,plain,(
% 0.21/0.53    $false | spl4_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f517,f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f143])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    spl4_6 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f517,plain,(
% 0.21/0.53    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f510,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f510,plain,(
% 0.21/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(resolution,[],[f505,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_pre_topc(X2,sK2) | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.53    inference(resolution,[],[f64,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    l1_pre_topc(sK2)),
% 0.21/0.53    inference(resolution,[],[f93,f55])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f63,f58])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.53  fof(f505,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f495,f95])).
% 0.21/0.53  fof(f495,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK2) | ~l1_pre_topc(sK2)),
% 0.21/0.53    inference(resolution,[],[f483,f340])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK1,sK1,sK1),X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f300,f329])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    k1_tsep_1(sK1,sK2,sK2) = k1_tsep_1(sK1,sK1,sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f286,f328])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK1,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f284,f56])).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    v2_struct_0(sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK1,sK1)),
% 0.21/0.53    inference(resolution,[],[f278,f219])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f215,f58])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.53    inference(resolution,[],[f213,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f152,f55])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) | ~m1_pre_topc(sK2,sK1)),
% 0.21/0.53    inference(superposition,[],[f147,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~m1_pre_topc(X0,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f65,f58])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f210,f58])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)) )),
% 0.21/0.53    inference(resolution,[],[f92,f57])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~v2_pre_topc(X2) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f85,f63])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK1,X0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f277,f58])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK1,X0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f274,f56])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK1,X0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f70,f57])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK2,sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f52,f285])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f281,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    v2_struct_0(sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK2,sK2)),
% 0.21/0.53    inference(resolution,[],[f278,f55])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK1,sK2,sK2),X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f213,f286])).
% 0.21/0.53  fof(f483,plain,(
% 0.21/0.53    m1_pre_topc(k1_tsep_1(sK1,sK1,sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f374,f480])).
% 0.21/0.53  fof(f480,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f479,f56])).
% 0.21/0.53  fof(f479,plain,(
% 0.21/0.53    v2_struct_0(sK1) | m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f478,f55])).
% 0.21/0.53  fof(f478,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK1) | m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f477,f54])).
% 0.21/0.53  % (1330)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  fof(f477,plain,(
% 0.21/0.53    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK1) | m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f476,f58])).
% 0.21/0.53  fof(f476,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK1) | m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f475,f57])).
% 0.21/0.53  fof(f475,plain,(
% 0.21/0.53    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK1) | m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f474])).
% 0.21/0.53  fof(f474,plain,(
% 0.21/0.53    k1_tsep_1(sK1,sK1,sK1) != k1_tsep_1(sK1,sK1,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK1) | m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f473])).
% 0.21/0.53  fof(f473,plain,(
% 0.21/0.53    k1_tsep_1(sK1,sK1,sK1) != k1_tsep_1(sK1,sK1,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK1) | m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(superposition,[],[f470,f329])).
% 0.21/0.53  fof(f470,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_tsep_1(sK1,sK1,sK1) != k1_tsep_1(X0,X1,sK2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f468,f54])).
% 0.21/0.53  fof(f468,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_tsep_1(sK1,sK1,sK1) != k1_tsep_1(X0,X1,sK2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,sK2)) )),
% 0.21/0.53    inference(superposition,[],[f71,f330])).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK1,sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f285,f329])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    m1_pre_topc(k1_tsep_1(sK1,sK1,sK1),sK2) | ~m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(superposition,[],[f149,f330])).
% 0.21/0.53  % (1349)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X2] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),sK2) | ~m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f65,f95])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl4_5 | ~spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f137,f143,f139])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f136,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.53    inference(resolution,[],[f135,f79])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.53    inference(resolution,[],[f132,f55])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK1) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(resolution,[],[f64,f58])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (1348)------------------------------
% 0.21/0.53  % (1348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1348)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (1348)Memory used [KB]: 11257
% 0.21/0.53  % (1348)Time elapsed: 0.097 s
% 0.21/0.53  % (1348)------------------------------
% 0.21/0.53  % (1348)------------------------------
% 0.21/0.53  % (1325)Success in time 0.168 s
%------------------------------------------------------------------------------
