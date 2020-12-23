%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:53 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 524 expanded)
%              Number of leaves         :   24 ( 143 expanded)
%              Depth                    :   51
%              Number of atoms          :  566 (2093 expanded)
%              Number of equality atoms :   39 ( 238 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(subsumption_resolution,[],[f279,f56])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

% (31658)Refutation not found, incomplete strategy% (31658)------------------------------
% (31658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31658)Termination reason: Refutation not found, incomplete strategy

% (31658)Memory used [KB]: 10618
% (31658)Time elapsed: 0.102 s
% (31658)------------------------------
% (31658)------------------------------
fof(f45,plain,
    ( ~ v1_tdlat_3(sK0)
    & ! [X1] :
        ( ! [X2] :
            ( v5_pre_topc(X2,sK0,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            | ~ v1_funct_1(X2) )
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ~ v1_tdlat_3(X0)
        & ! [X1] :
            ( ! [X2] :
                ( v5_pre_topc(X2,X0,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
            | ~ l1_pre_topc(X1)
            | ~ v2_pre_topc(X1)
            | v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v1_tdlat_3(sK0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,sK0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( ( l1_pre_topc(X1)
                & v2_pre_topc(X1)
                & ~ v2_struct_0(X1) )
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                 => v5_pre_topc(X2,X0,X1) ) )
         => v1_tdlat_3(X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tex_2)).

fof(f279,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f278,f83])).

fof(f83,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f278,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f276,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f276,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f275,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f275,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f274,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f76,f88])).

fof(f88,plain,(
    ! [X0] : k1_compts_1(X0) = g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0))) ),
    inference(definition_unfolding,[],[f77,f85])).

fof(f85,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f77,plain,(
    ! [X0] : k1_compts_1(X0) = g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_compts_1(X0) = g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_compts_1)).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k1_compts_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k1_compts_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k1_compts_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_compts_1)).

fof(f274,plain,(
    v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f273,f55])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f273,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f272,f56])).

fof(f272,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f270,f58])).

fof(f58,plain,(
    ~ v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f270,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f269,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(sK1(X0),X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f269,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f268,f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f82,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f268,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f267,f87])).

fof(f87,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f267,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v1_funct_1(k6_relat_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f266,f91])).

fof(f91,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f72,f82])).

fof(f72,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f266,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v1_partfun1(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_relat_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f265,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f265,plain,
    ( ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | v4_pre_topc(sK1(sK0),sK0)
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f264,f92])).

fof(f92,plain,(
    ! [X0] : l1_pre_topc(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))) ),
    inference(definition_unfolding,[],[f75,f88])).

fof(f75,plain,(
    ! [X0] : l1_pre_topc(k1_compts_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : l1_pre_topc(k1_compts_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_compts_1)).

fof(f264,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f263,f89])).

fof(f89,plain,(
    ! [X0] : v1_tdlat_3(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))) ),
    inference(definition_unfolding,[],[f63,f88])).

fof(f63,plain,(
    ! [X0] : v1_tdlat_3(k1_compts_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_tdlat_3(k1_compts_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tex_1)).

fof(f263,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v1_tdlat_3(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(resolution,[],[f187,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f187,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v4_pre_topc(sK1(sK0),sK0)
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(forward_demodulation,[],[f186,f140])).

fof(f140,plain,(
    ! [X0] : u1_struct_0(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))) = X0 ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0))) != g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))
      | u1_struct_0(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))) = X1 ) ),
    inference(resolution,[],[f126,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f126,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7)))
      | u1_struct_0(g1_pre_topc(X6,k2_subset_1(k1_zfmisc_1(X6)))) = X7
      | g1_pre_topc(X6,k2_subset_1(k1_zfmisc_1(X6))) != g1_pre_topc(X7,X8) ) ),
    inference(superposition,[],[f68,f99])).

fof(f99,plain,(
    ! [X0] : g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0))) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))),u1_pre_topc(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0))))) ),
    inference(subsumption_resolution,[],[f98,f92])).

fof(f98,plain,(
    ! [X0] :
      ( g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0))) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))),u1_pre_topc(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))))
      | ~ l1_pre_topc(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))) ) ),
    inference(resolution,[],[f86,f96])).

fof(f96,plain,(
    ! [X0] : v1_pre_topc(g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0)))) ),
    inference(resolution,[],[f80,f84])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f186,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f185,f90])).

fof(f185,plain,
    ( ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v4_pre_topc(sK1(sK0),sK0)
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(forward_demodulation,[],[f184,f140])).

fof(f184,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f183,f92])).

% (31665)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (31674)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (31669)Refutation not found, incomplete strategy% (31669)------------------------------
% (31669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31664)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (31667)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (31669)Termination reason: Refutation not found, incomplete strategy

% (31669)Memory used [KB]: 10746
% (31669)Time elapsed: 0.104 s
% (31669)------------------------------
% (31669)------------------------------
% (31663)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (31667)Refutation not found, incomplete strategy% (31667)------------------------------
% (31667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31667)Termination reason: Refutation not found, incomplete strategy

% (31667)Memory used [KB]: 10746
% (31667)Time elapsed: 0.139 s
% (31667)------------------------------
% (31667)------------------------------
% (31668)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (31668)Refutation not found, incomplete strategy% (31668)------------------------------
% (31668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31659)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (31660)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (31661)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (31655)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (31656)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (31655)Refutation not found, incomplete strategy% (31655)------------------------------
% (31655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31648)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (31649)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (31668)Termination reason: Refutation not found, incomplete strategy
% (31672)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark

% (31668)Memory used [KB]: 1663
% (31668)Time elapsed: 0.139 s
% (31668)------------------------------
% (31668)------------------------------
% (31655)Termination reason: Refutation not found, incomplete strategy

% (31655)Memory used [KB]: 10746
% (31655)Time elapsed: 0.149 s
% (31655)------------------------------
% (31655)------------------------------
% (31657)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (31673)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (31656)Refutation not found, incomplete strategy% (31656)------------------------------
% (31656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31656)Termination reason: Refutation not found, incomplete strategy

% (31656)Memory used [KB]: 10618
% (31656)Time elapsed: 0.158 s
% (31656)------------------------------
% (31656)------------------------------
% (31649)Refutation not found, incomplete strategy% (31649)------------------------------
% (31649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31649)Termination reason: Refutation not found, incomplete strategy

% (31649)Memory used [KB]: 10746
% (31649)Time elapsed: 0.129 s
% (31649)------------------------------
% (31649)------------------------------
% (31664)Refutation not found, incomplete strategy% (31664)------------------------------
% (31664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31664)Termination reason: Refutation not found, incomplete strategy

% (31664)Memory used [KB]: 10618
% (31664)Time elapsed: 0.156 s
% (31664)------------------------------
% (31664)------------------------------
fof(f183,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f179,f87])).

fof(f179,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ v1_funct_1(k6_relat_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    inference(resolution,[],[f178,f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( v5_pre_topc(X2,sK0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f178,plain,
    ( ~ v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),sK0,g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v4_pre_topc(sK1(sK0),sK0) ),
    inference(forward_demodulation,[],[f177,f120])).

fof(f120,plain,(
    sK1(sK0) = k10_relat_1(k6_relat_1(u1_struct_0(sK0)),sK1(sK0)) ),
    inference(subsumption_resolution,[],[f119,f56])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1(sK0) = k10_relat_1(k6_relat_1(u1_struct_0(sK0)),sK1(sK0)) ),
    inference(subsumption_resolution,[],[f116,f58])).

fof(f116,plain,
    ( v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | sK1(sK0) = k10_relat_1(k6_relat_1(u1_struct_0(sK0)),sK1(sK0)) ),
    inference(resolution,[],[f110,f55])).

fof(f110,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(X2)
      | v1_tdlat_3(X2)
      | ~ l1_pre_topc(X2)
      | sK1(X2) = k10_relat_1(k6_relat_1(u1_struct_0(X2)),sK1(X2)) ) ),
    inference(backward_demodulation,[],[f102,f108])).

fof(f108,plain,(
    ! [X4,X3] : k8_relset_1(X3,X3,k6_relat_1(X3),X4) = k10_relat_1(k6_relat_1(X3),X4) ),
    inference(resolution,[],[f78,f90])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f102,plain,(
    ! [X2] :
      ( sK1(X2) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X2),k6_relat_1(u1_struct_0(X2)),sK1(X2))
      | v1_tdlat_3(X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f177,plain,
    ( ~ v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),sK0,g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(sK0)),sK1(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f176,f55])).

fof(f176,plain,
    ( ~ v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),sK0,g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(sK0)),sK1(sK0)),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f175,f56])).

fof(f175,plain,
    ( ~ v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),sK0,g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(sK0)),sK1(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f173,f58])).

fof(f173,plain,
    ( ~ v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),sK0,g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(sK0)),sK1(sK0)),sK0)
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f167,f60])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),sK0,g1_pre_topc(u1_struct_0(sK0),k2_subset_1(k1_zfmisc_1(u1_struct_0(sK0)))))
      | v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(sK0)),X0),sK0) ) ),
    inference(resolution,[],[f165,f56])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(k6_relat_1(u1_struct_0(X0)),X0,g1_pre_topc(u1_struct_0(X0),k2_subset_1(k1_zfmisc_1(u1_struct_0(X0)))))
      | v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(X0)),X1),X0) ) ),
    inference(subsumption_resolution,[],[f164,f90])).

fof(f164,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(X0)),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(k6_relat_1(u1_struct_0(X0)),X0,g1_pre_topc(u1_struct_0(X0),k2_subset_1(k1_zfmisc_1(u1_struct_0(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k6_relat_1(u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f163,f87])).

fof(f163,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(X0)),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(k6_relat_1(u1_struct_0(X0)),X0,g1_pre_topc(u1_struct_0(X0),k2_subset_1(k1_zfmisc_1(u1_struct_0(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(k6_relat_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k6_relat_1(u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f161,f91])).

fof(f161,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(X0)),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(k6_relat_1(u1_struct_0(X0)),X0,g1_pre_topc(u1_struct_0(X0),k2_subset_1(k1_zfmisc_1(u1_struct_0(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v1_partfun1(k6_relat_1(u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(k6_relat_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k6_relat_1(u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f159,f71])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k6_relat_1(u1_struct_0(X0)),u1_struct_0(X0),u1_struct_0(X0))
      | v4_pre_topc(k10_relat_1(k6_relat_1(u1_struct_0(X0)),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(k6_relat_1(u1_struct_0(X0)),X0,g1_pre_topc(u1_struct_0(X0),k2_subset_1(k1_zfmisc_1(u1_struct_0(X0)))))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f157,f108])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k6_relat_1(u1_struct_0(X0)),u1_struct_0(X0),u1_struct_0(X0))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k6_relat_1(u1_struct_0(X0)),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(k6_relat_1(u1_struct_0(X0)),X0,g1_pre_topc(u1_struct_0(X0),k2_subset_1(k1_zfmisc_1(u1_struct_0(X0)))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f156,f90])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),X1)))
      | ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),X1,k6_relat_1(X2),X0),X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ l1_pre_topc(X3) ) ),
    inference(forward_demodulation,[],[f155,f140])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),X1)
      | ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))),k6_relat_1(X2),X0),X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(forward_demodulation,[],[f154,f140])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))),k6_relat_1(X2),X0),X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(forward_demodulation,[],[f153,f140])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))))
      | ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))),k6_relat_1(X2),X0),X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))))
      | ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))),k6_relat_1(X2),X0),X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(forward_demodulation,[],[f151,f140])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))))
      | ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))),k6_relat_1(X2),X0),X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f150,f92])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))))
      | ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))),k6_relat_1(X2),X0),X3)
      | ~ l1_pre_topc(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f149,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X0,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(backward_demodulation,[],[f104,f140])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X0,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))))) ) ),
    inference(subsumption_resolution,[],[f103,f92])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))))
      | v4_pre_topc(X0,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
      | ~ l1_pre_topc(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ) ),
    inference(resolution,[],[f95,f89])).

fof(f95,plain,(
    ! [X2,X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f59,f62])).

fof(f59,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,X1)
      | ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),k6_relat_1(X2),X0),X3)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f64,f87])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
                    & v4_pre_topc(sK2(X0,X1,X2),X1)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v4_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

%------------------------------------------------------------------------------
