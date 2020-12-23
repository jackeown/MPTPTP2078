%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:35 EST 2020

% Result     : Theorem 2.96s
% Output     : Refutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  464 (3891 expanded)
%              Number of leaves         :   35 (1295 expanded)
%              Depth                    :   32
%              Number of atoms          : 2654 (38814 expanded)
%              Number of equality atoms :  131 (3891 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4046,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f111,f206,f217,f235,f315,f323,f495,f510,f522,f543,f545,f689,f698,f710,f775,f1817,f1866,f1950,f2151,f2230,f2415,f2676,f2786,f2809,f3288,f3327,f3416,f4045])).

fof(f4045,plain,
    ( spl4_1
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_30
    | ~ spl4_73 ),
    inference(avatar_contradiction_clause,[],[f4044])).

fof(f4044,plain,
    ( $false
    | spl4_1
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_30
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f4043,f1615])).

fof(f1615,plain,(
    ! [X17] : v1_funct_2(k1_xboole_0,k1_xboole_0,X17) ),
    inference(subsumption_resolution,[],[f837,f1612])).

fof(f1612,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f343,f844])).

fof(f844,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f167,f72])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f167,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f162,f157])).

fof(f157,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f162,plain,(
    ! [X0,X1] : m1_subset_1(k1_relset_1(X0,X1,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f78,f61])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f343,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f122,f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f122,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f72,f61])).

fof(f837,plain,(
    ! [X17] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X17) ) ),
    inference(forward_demodulation,[],[f835,f157])).

fof(f835,plain,(
    ! [X17] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X17)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X17,k1_xboole_0) ) ),
    inference(resolution,[],[f123,f117])).

fof(f117,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f96,f92])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f96,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f123,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f73,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4043,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_1
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_30
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f4042,f1612])).

fof(f4042,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl4_1
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_30
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f4041,f661])).

fof(f661,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f659])).

fof(f659,plain,
    ( spl4_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f4041,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | spl4_1
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f4040,f205])).

fof(f205,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_12
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f4040,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f4039,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f4039,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f4038,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f4038,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f4037,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f4037,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f4036,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f4036,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f4035,f114])).

fof(f114,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f55,f58])).

fof(f58,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f4035,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f4034,f105])).

fof(f105,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f4034,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f4033,f2950])).

fof(f2950,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f2949])).

fof(f2949,plain,
    ( spl4_73
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f4033,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_13
    | ~ spl4_23 ),
    inference(resolution,[],[f3603,f509])).

fof(f509,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl4_23
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f3603,plain,
    ( ! [X6,X7] :
        ( ~ v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f3602,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3602,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f3601,f50])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f3601,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f3563,f51])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f3563,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_13 ),
    inference(superposition,[],[f101,f212])).

fof(f212,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_13
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f3416,plain,
    ( ~ spl4_12
    | ~ spl4_13
    | spl4_14
    | spl4_73 ),
    inference(avatar_contradiction_clause,[],[f3415])).

fof(f3415,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_13
    | spl4_14
    | spl4_73 ),
    inference(global_subsumption,[],[f602,f2951])).

fof(f2951,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_73 ),
    inference(avatar_component_clause,[],[f2949])).

fof(f602,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f588,f91])).

fof(f588,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_13 ),
    inference(superposition,[],[f112,f212])).

fof(f112,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f57,f58])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f39])).

fof(f3327,plain,
    ( spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f3326])).

fof(f3326,plain,
    ( $false
    | spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3325,f50])).

fof(f3325,plain,
    ( ~ v2_pre_topc(sK1)
    | spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3324,f51])).

fof(f3324,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3323,f114])).

fof(f3323,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3322,f105])).

fof(f3322,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3321,f520])).

fof(f520,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl4_25
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f3321,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3319,f516])).

fof(f516,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl4_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f3319,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(resolution,[],[f2901,f3270])).

fof(f3270,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f310,f205])).

fof(f310,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl4_17
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f2901,plain,
    ( ! [X4,X5] :
        ( ~ v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f2900])).

fof(f2900,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | ~ v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5)
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f2899,f2821])).

fof(f2821,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f216,f205])).

fof(f216,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl4_14
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f2899,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | ~ v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5)
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f2898])).

fof(f2898,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | ~ v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5)
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f2897,f2821])).

fof(f2897,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5))))
        | ~ v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5)
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2896,f48])).

fof(f2896,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5))))
        | ~ v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5)
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2869,f49])).

fof(f2869,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5))))
        | ~ v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5)
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_12 ),
    inference(superposition,[],[f99,f205])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f3288,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f3287])).

fof(f3287,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3286,f520])).

fof(f3286,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f3285,f2821])).

fof(f3285,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f3284,f205])).

fof(f3284,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3283,f516])).

fof(f3283,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f3265,f2821])).

fof(f3265,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f3264,f205])).

fof(f3264,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3263,f3259])).

fof(f3259,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3258,f50])).

fof(f3258,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3257,f51])).

fof(f3257,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3245,f114])).

fof(f3245,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3244,f104])).

fof(f104,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f3244,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f3225,f520])).

fof(f3225,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(resolution,[],[f2893,f516])).

fof(f2893,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,sK0,X1)
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f2892])).

fof(f2892,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,sK0,X1)
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f2891,f2821])).

fof(f2891,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,sK0,X1)
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f2890])).

fof(f2890,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,sK0,X1)
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f2889,f2821])).

fof(f2889,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,sK0,X1)
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2888,f48])).

fof(f2888,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,sK0,X1)
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2867,f49])).

fof(f2867,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,sK0,X1)
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_12 ),
    inference(superposition,[],[f98,f205])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3263,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f3262,f205])).

fof(f3262,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f1911,f2491])).

fof(f2491,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_2 ),
    inference(forward_demodulation,[],[f109,f58])).

fof(f109,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1911,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1910,f141])).

fof(f141,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f139,f49])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f63,f48])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f1910,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f1909,f292])).

fof(f292,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f125,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f125,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f1909,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f1908,f50])).

fof(f1908,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f1907,f51])).

fof(f1907,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f1906,f114])).

fof(f1906,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f238,f113])).

fof(f113,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f56,f58])).

fof(f56,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f238,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f100,f112])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2809,plain,
    ( spl4_15
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f2808])).

fof(f2808,plain,
    ( $false
    | spl4_15
    | ~ spl4_30 ),
    inference(global_subsumption,[],[f1421,f231])).

fof(f231,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl4_15
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1421,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_30 ),
    inference(superposition,[],[f114,f661])).

fof(f2786,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f2785])).

fof(f2785,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2784,f1615])).

fof(f2784,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2783,f661])).

fof(f2783,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2782,f2486])).

fof(f2486,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2485,f1612])).

fof(f2485,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f205,f661])).

fof(f2782,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2781,f61])).

fof(f2781,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2780,f661])).

fof(f2780,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2779,f92])).

fof(f2779,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2778,f2486])).

fof(f2778,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2777,f2555])).

fof(f2555,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_2
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(superposition,[],[f2492,f2486])).

fof(f2492,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_2
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2491,f661])).

fof(f2777,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2776,f661])).

fof(f2776,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2775,f2486])).

fof(f2775,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2429,f2774])).

fof(f2774,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2773,f50])).

fof(f2773,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2768,f51])).

fof(f2768,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(resolution,[],[f2653,f2495])).

fof(f2495,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_1
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f104,f661])).

fof(f2653,plain,
    ( ! [X22] :
        ( ~ v5_pre_topc(k1_xboole_0,sK0,X22)
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ l1_pre_topc(X22)
        | ~ v2_pre_topc(X22) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2652,f48])).

fof(f2652,plain,
    ( ! [X22] :
        ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X22)
        | ~ l1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2651,f49])).

fof(f2651,plain,
    ( ! [X22] :
        ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X22)
        | ~ l1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2650,f1615])).

fof(f2650,plain,
    ( ! [X22] :
        ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X22)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X22))
        | ~ l1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2568,f1615])).

fof(f2568,plain,
    ( ! [X22] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X22)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X22))
        | ~ l1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(superposition,[],[f715,f2486])).

fof(f715,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f693,f230])).

fof(f230,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f229])).

fof(f693,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f239,f61])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f100,f61])).

fof(f2429,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2135,f661])).

fof(f2135,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f2134,f48])).

fof(f2134,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f2133,f49])).

fof(f2133,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f2132,f142])).

fof(f142,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f140,f51])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f63,f50])).

fof(f2132,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f2131,f188])).

fof(f188,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_10
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f2131,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2130,f114])).

fof(f2130,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f225,f113])).

fof(f225,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f98,f112])).

fof(f2676,plain,
    ( ~ spl4_12
    | spl4_21
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f2675])).

fof(f2675,plain,
    ( $false
    | ~ spl4_12
    | spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2674,f1615])).

fof(f2674,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_12
    | spl4_21
    | ~ spl4_30 ),
    inference(superposition,[],[f2420,f2486])).

fof(f2420,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f501,f661])).

fof(f501,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl4_21
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f2415,plain,
    ( spl4_1
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f2414])).

fof(f2414,plain,
    ( $false
    | spl4_1
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2413,f1339])).

fof(f1339,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1305,f661])).

fof(f1305,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f53,f201])).

fof(f201,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_11
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f2413,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | spl4_1
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2412,f201])).

fof(f2412,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl4_1
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2411,f50])).

fof(f2411,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | spl4_1
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2410,f51])).

fof(f2410,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl4_1
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2409,f2184])).

fof(f2184,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl4_1
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f105,f661])).

fof(f2409,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(resolution,[],[f2327,f2180])).

fof(f2180,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f310,f661])).

fof(f2327,plain,
    ( ! [X9] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(k1_xboole_0,sK0,X9)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2326,f48])).

fof(f2326,plain,
    ( ! [X9] :
        ( v5_pre_topc(k1_xboole_0,sK0,X9)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X9)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2325,f49])).

fof(f2325,plain,
    ( ! [X9] :
        ( v5_pre_topc(k1_xboole_0,sK0,X9)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X9)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2278,f1615])).

fof(f2278,plain,
    ( ! [X9] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X9))
        | v5_pre_topc(k1_xboole_0,sK0,X9)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X9)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(superposition,[],[f714,f2243])).

fof(f2243,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_14
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2242,f1612])).

fof(f2242,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl4_14
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f216,f661])).

fof(f714,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f696,f230])).

fof(f696,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f237,f61])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f99,f61])).

fof(f2230,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f2229])).

fof(f2229,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2228,f48])).

fof(f2228,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2227,f49])).

fof(f2227,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2226,f1339])).

fof(f2226,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2200,f2214])).

fof(f2214,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2213,f1958])).

fof(f1958,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl4_11
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1957,f661])).

fof(f1957,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f500,f201])).

fof(f500,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f499])).

fof(f2213,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2212,f661])).

fof(f2212,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2211,f201])).

fof(f2211,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2210,f61])).

fof(f2210,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2209,f661])).

fof(f2209,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2208,f201])).

fof(f2208,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2207,f661])).

fof(f2207,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2206,f201])).

fof(f2206,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2159,f2183])).

fof(f2183,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_2
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2182,f661])).

fof(f2182,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f2181,f58])).

fof(f2181,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f108,f201])).

fof(f108,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f2159,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2158,f661])).

fof(f2158,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f2157,f201])).

fof(f2157,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f2156,f48])).

fof(f2156,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f2155,f49])).

fof(f2155,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f2154,f142])).

fof(f2154,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f2153,f188])).

fof(f2153,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2152,f114])).

fof(f2152,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f236,f113])).

fof(f236,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f99,f112])).

fof(f2200,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2194,f2184])).

fof(f2194,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(resolution,[],[f1409,f1958])).

fof(f1409,plain,
    ( ! [X23] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X23,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0)
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(X23) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1408,f50])).

fof(f1408,plain,
    ( ! [X23] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X23,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(X23) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1338,f51])).

fof(f1338,plain,
    ( ! [X23] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X23,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(X23) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(superposition,[],[f716,f201])).

fof(f716,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f690,f230])).

fof(f690,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f280,f61])).

fof(f280,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f101,f61])).

fof(f2151,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f2150])).

fof(f2150,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2149,f1339])).

fof(f2149,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2148,f661])).

fof(f2148,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2147,f1963])).

fof(f1963,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f212,f201])).

fof(f2147,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2146,f201])).

fof(f2146,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2145,f61])).

fof(f2145,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2144,f661])).

fof(f2144,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2143,f91])).

fof(f2143,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2142,f1963])).

fof(f2142,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2141,f201])).

fof(f2141,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2140,f1936])).

fof(f1936,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_2
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1935,f661])).

fof(f1935,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_2
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1934,f58])).

fof(f1934,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_2
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f109,f201])).

fof(f2140,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2139,f661])).

fof(f2139,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2138,f201])).

fof(f2138,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2137,f2125])).

fof(f2125,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2124,f48])).

fof(f2124,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2123,f49])).

fof(f2123,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2122,f1339])).

fof(f2122,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2106,f1937])).

fof(f1937,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_1
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f104,f661])).

fof(f2106,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(resolution,[],[f1405,f1958])).

fof(f1405,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1404,f50])).

fof(f1404,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1336,f51])).

fof(f1336,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(superposition,[],[f715,f201])).

fof(f2137,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f2136,f661])).

fof(f2136,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f2135,f201])).

fof(f1950,plain,
    ( spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f1949])).

fof(f1949,plain,
    ( $false
    | spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1948,f1938])).

fof(f1938,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_18
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f313,f661])).

fof(f313,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl4_18
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1948,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1947,f661])).

fof(f1947,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1946,f201])).

fof(f1946,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1945,f61])).

fof(f1945,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1944,f661])).

fof(f1944,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1943,f91])).

fof(f1943,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1942,f201])).

fof(f1942,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1941,f1936])).

fof(f1941,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1940,f661])).

fof(f1940,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1939,f201])).

fof(f1939,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1912,f1933])).

fof(f1933,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f310,f661])).

fof(f1912,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1911,f661])).

fof(f1866,plain,
    ( ~ spl4_14
    | spl4_18
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f1865])).

fof(f1865,plain,
    ( $false
    | ~ spl4_14
    | spl4_18
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1864,f1615])).

fof(f1864,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_14
    | spl4_18
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1863,f661])).

fof(f1863,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_14
    | spl4_18
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1862,f1612])).

fof(f1862,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_14
    | spl4_18
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f314,f1297])).

fof(f1297,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl4_14
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f216,f661])).

fof(f314,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f312])).

fof(f1817,plain,
    ( ~ spl4_1
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | spl4_17
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f1816])).

fof(f1816,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1815,f1615])).

fof(f1815,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | spl4_17
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1814,f1612])).

fof(f1814,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1813,f1429])).

fof(f1429,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl4_17
    | ~ spl4_30 ),
    inference(superposition,[],[f309,f661])).

fof(f309,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f308])).

fof(f1813,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1802,f1418])).

fof(f1418,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_1
    | ~ spl4_30 ),
    inference(superposition,[],[f104,f661])).

fof(f1802,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1801,f51])).

fof(f1801,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1800,f50])).

fof(f1800,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1798,f1339])).

fof(f1798,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(superposition,[],[f1492,f201])).

fof(f1492,plain,
    ( ! [X8] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X8))
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X8))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X8)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X8) )
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1491,f49])).

fof(f1491,plain,
    ( ! [X8] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X8))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X8))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X8)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X8) )
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1455,f48])).

fof(f1455,plain,
    ( ! [X8] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X8))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X8))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X8)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X8) )
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(superposition,[],[f234,f1297])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f775,plain,
    ( ~ spl4_13
    | spl4_30 ),
    inference(avatar_contradiction_clause,[],[f774])).

fof(f774,plain,
    ( $false
    | ~ spl4_13
    | spl4_30 ),
    inference(subsumption_resolution,[],[f773,f122])).

fof(f773,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_13
    | spl4_30 ),
    inference(subsumption_resolution,[],[f771,f660])).

fof(f660,plain,
    ( k1_xboole_0 != sK2
    | spl4_30 ),
    inference(avatar_component_clause,[],[f659])).

fof(f771,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_13 ),
    inference(resolution,[],[f649,f71])).

fof(f649,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_13 ),
    inference(resolution,[],[f602,f72])).

fof(f710,plain,
    ( ~ spl4_11
    | spl4_30 ),
    inference(avatar_contradiction_clause,[],[f709])).

fof(f709,plain,
    ( $false
    | ~ spl4_11
    | spl4_30 ),
    inference(global_subsumption,[],[f318,f660])).

fof(f318,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f316,f122])).

fof(f316,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_11 ),
    inference(resolution,[],[f254,f71])).

fof(f254,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f245,f91])).

fof(f245,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl4_11 ),
    inference(superposition,[],[f120,f201])).

fof(f120,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f72,f54])).

fof(f698,plain,
    ( ~ spl4_11
    | ~ spl4_13
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f697])).

fof(f697,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_13
    | spl4_21 ),
    inference(global_subsumption,[],[f240,f683])).

fof(f683,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_13
    | spl4_21 ),
    inference(forward_demodulation,[],[f501,f212])).

fof(f240,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f53,f201])).

fof(f689,plain,
    ( ~ spl4_13
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl4_13
    | spl4_22 ),
    inference(subsumption_resolution,[],[f687,f602])).

fof(f687,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_13
    | spl4_22 ),
    inference(forward_demodulation,[],[f686,f91])).

fof(f686,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl4_13
    | spl4_22 ),
    inference(forward_demodulation,[],[f505,f212])).

fof(f505,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl4_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f545,plain,
    ( ~ spl4_12
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl4_12
    | spl4_24 ),
    inference(subsumption_resolution,[],[f526,f517])).

fof(f517,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f515])).

fof(f526,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl4_12 ),
    inference(superposition,[],[f54,f205])).

fof(f543,plain,
    ( ~ spl4_12
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl4_12
    | spl4_25 ),
    inference(subsumption_resolution,[],[f525,f521])).

fof(f521,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f519])).

fof(f525,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl4_12 ),
    inference(superposition,[],[f53,f205])).

fof(f522,plain,
    ( ~ spl4_24
    | ~ spl4_25
    | ~ spl4_2
    | ~ spl4_14
    | spl4_17 ),
    inference(avatar_split_clause,[],[f513,f308,f214,f107,f519,f515])).

fof(f513,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_14
    | spl4_17 ),
    inference(forward_demodulation,[],[f512,f216])).

fof(f512,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_14
    | spl4_17 ),
    inference(forward_demodulation,[],[f511,f216])).

fof(f511,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_2
    | spl4_17 ),
    inference(subsumption_resolution,[],[f302,f309])).

fof(f302,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f301,f141])).

fof(f301,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f300,f292])).

fof(f300,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f299,f50])).

fof(f299,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f298,f51])).

fof(f298,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f297,f114])).

fof(f297,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f296,f113])).

fof(f296,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f279,f119])).

fof(f119,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f108,f58])).

fof(f279,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f101,f112])).

fof(f510,plain,
    ( ~ spl4_21
    | ~ spl4_22
    | spl4_23
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f497,f187,f107,f507,f503,f499])).

fof(f497,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f331,f188])).

fof(f331,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f330,f48])).

fof(f330,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f329,f49])).

fof(f329,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f328,f142])).

fof(f328,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f327,f114])).

fof(f327,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f326,f113])).

fof(f326,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f236,f119])).

fof(f495,plain,
    ( ~ spl4_11
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl4_11
    | spl4_15 ),
    inference(subsumption_resolution,[],[f486,f231])).

fof(f486,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f114,f318])).

fof(f323,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f319,f189])).

fof(f189,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f187])).

fof(f319,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f126,f68])).

fof(f126,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f62,f51])).

fof(f315,plain,
    ( spl4_17
    | ~ spl4_18
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f306,f199,f107,f312,f308])).

fof(f306,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f305,f201])).

fof(f305,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f304,f253])).

fof(f253,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f241,f91])).

fof(f241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl4_11 ),
    inference(superposition,[],[f54,f201])).

fof(f304,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f303,f91])).

fof(f303,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f302,f201])).

fof(f235,plain,
    ( ~ spl4_15
    | spl4_16 ),
    inference(avatar_split_clause,[],[f227,f233,f229])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f226,f61])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f98,f61])).

fof(f217,plain,
    ( spl4_13
    | spl4_14 ),
    inference(avatar_split_clause,[],[f208,f214,f210])).

fof(f208,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f207,f156])).

fof(f156,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    inference(resolution,[],[f77,f112])).

fof(f207,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    inference(subsumption_resolution,[],[f192,f113])).

fof(f192,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    inference(resolution,[],[f79,f112])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f206,plain,
    ( spl4_11
    | spl4_12 ),
    inference(avatar_split_clause,[],[f197,f203,f199])).

fof(f197,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f196,f155])).

fof(f155,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f77,f54])).

fof(f196,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f191,f53])).

fof(f191,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(resolution,[],[f79,f54])).

fof(f111,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f59,f107,f103])).

fof(f59,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f60,f107,f103])).

fof(f60,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (20147)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.46  % (20139)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (20131)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (20127)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (20128)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (20137)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (20142)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (20140)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (20146)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (20125)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (20148)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (20136)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (20124)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (20135)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (20138)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (20124)Refutation not found, incomplete strategy% (20124)------------------------------
% 0.21/0.52  % (20124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20124)Memory used [KB]: 10618
% 0.21/0.52  % (20124)Time elapsed: 0.108 s
% 0.21/0.52  % (20124)------------------------------
% 0.21/0.52  % (20124)------------------------------
% 0.21/0.52  % (20129)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (20143)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (20149)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (20132)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (20141)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (20126)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (20130)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (20145)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (20130)Refutation not found, incomplete strategy% (20130)------------------------------
% 0.21/0.54  % (20130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20130)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20130)Memory used [KB]: 10746
% 0.21/0.54  % (20130)Time elapsed: 0.087 s
% 0.21/0.54  % (20130)------------------------------
% 0.21/0.54  % (20130)------------------------------
% 0.21/0.54  % (20137)Refutation not found, incomplete strategy% (20137)------------------------------
% 0.21/0.54  % (20137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20135)Refutation not found, incomplete strategy% (20135)------------------------------
% 0.21/0.54  % (20135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20144)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.51/0.55  % (20137)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (20137)Memory used [KB]: 6268
% 1.51/0.55  % (20137)Time elapsed: 0.128 s
% 1.51/0.55  % (20137)------------------------------
% 1.51/0.55  % (20137)------------------------------
% 1.51/0.55  % (20135)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (20135)Memory used [KB]: 10874
% 1.51/0.55  % (20135)Time elapsed: 0.142 s
% 1.51/0.55  % (20135)------------------------------
% 1.51/0.55  % (20135)------------------------------
% 1.51/0.55  % (20133)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.51/0.55  % (20134)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.69/0.62  % (20125)Refutation not found, incomplete strategy% (20125)------------------------------
% 1.69/0.62  % (20125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.63  % (20125)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.63  
% 2.11/0.63  % (20125)Memory used [KB]: 11769
% 2.11/0.63  % (20125)Time elapsed: 0.209 s
% 2.11/0.63  % (20125)------------------------------
% 2.11/0.63  % (20125)------------------------------
% 2.38/0.66  % (20133)Refutation not found, incomplete strategy% (20133)------------------------------
% 2.38/0.66  % (20133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.66  % (20133)Termination reason: Refutation not found, incomplete strategy
% 2.38/0.66  
% 2.38/0.66  % (20133)Memory used [KB]: 6268
% 2.38/0.66  % (20133)Time elapsed: 0.244 s
% 2.38/0.66  % (20133)------------------------------
% 2.38/0.66  % (20133)------------------------------
% 2.96/0.77  % (20134)Refutation found. Thanks to Tanya!
% 2.96/0.77  % SZS status Theorem for theBenchmark
% 2.96/0.77  % SZS output start Proof for theBenchmark
% 2.96/0.77  fof(f4046,plain,(
% 2.96/0.77    $false),
% 2.96/0.77    inference(avatar_sat_refutation,[],[f110,f111,f206,f217,f235,f315,f323,f495,f510,f522,f543,f545,f689,f698,f710,f775,f1817,f1866,f1950,f2151,f2230,f2415,f2676,f2786,f2809,f3288,f3327,f3416,f4045])).
% 2.96/0.77  fof(f4045,plain,(
% 2.96/0.77    spl4_1 | ~spl4_12 | ~spl4_13 | ~spl4_23 | ~spl4_30 | ~spl4_73),
% 2.96/0.77    inference(avatar_contradiction_clause,[],[f4044])).
% 2.96/0.77  fof(f4044,plain,(
% 2.96/0.77    $false | (spl4_1 | ~spl4_12 | ~spl4_13 | ~spl4_23 | ~spl4_30 | ~spl4_73)),
% 2.96/0.77    inference(subsumption_resolution,[],[f4043,f1615])).
% 2.96/0.77  fof(f1615,plain,(
% 2.96/0.77    ( ! [X17] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X17)) )),
% 2.96/0.77    inference(subsumption_resolution,[],[f837,f1612])).
% 2.96/0.77  fof(f1612,plain,(
% 2.96/0.77    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.96/0.77    inference(resolution,[],[f343,f844])).
% 2.96/0.77  fof(f844,plain,(
% 2.96/0.77    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 2.96/0.77    inference(resolution,[],[f167,f72])).
% 2.96/0.77  fof(f72,plain,(
% 2.96/0.77    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.96/0.77    inference(cnf_transformation,[],[f44])).
% 2.96/0.77  fof(f44,plain,(
% 2.96/0.77    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.96/0.77    inference(nnf_transformation,[],[f4])).
% 2.96/0.77  fof(f4,axiom,(
% 2.96/0.77    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.96/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.96/0.77  fof(f167,plain,(
% 2.96/0.77    ( ! [X0] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.96/0.77    inference(forward_demodulation,[],[f162,f157])).
% 2.96/0.77  fof(f157,plain,(
% 2.96/0.77    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 2.96/0.77    inference(resolution,[],[f77,f61])).
% 2.96/0.77  fof(f61,plain,(
% 2.96/0.77    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.96/0.77    inference(cnf_transformation,[],[f3])).
% 2.96/0.77  fof(f3,axiom,(
% 2.96/0.77    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.96/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.96/0.77  fof(f77,plain,(
% 2.96/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.96/0.77    inference(cnf_transformation,[],[f29])).
% 2.96/0.77  fof(f29,plain,(
% 2.96/0.77    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.77    inference(ennf_transformation,[],[f7])).
% 2.96/0.77  fof(f7,axiom,(
% 2.96/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.96/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.96/0.77  fof(f162,plain,(
% 2.96/0.77    ( ! [X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.96/0.77    inference(resolution,[],[f78,f61])).
% 2.96/0.77  fof(f78,plain,(
% 2.96/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 2.96/0.77    inference(cnf_transformation,[],[f30])).
% 2.96/0.77  fof(f30,plain,(
% 2.96/0.77    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.77    inference(ennf_transformation,[],[f6])).
% 2.96/0.77  fof(f6,axiom,(
% 2.96/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.96/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 2.96/0.77  fof(f343,plain,(
% 2.96/0.77    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.96/0.77    inference(resolution,[],[f122,f71])).
% 2.96/0.77  fof(f71,plain,(
% 2.96/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.96/0.77    inference(cnf_transformation,[],[f43])).
% 2.96/0.77  fof(f43,plain,(
% 2.96/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.96/0.77    inference(flattening,[],[f42])).
% 2.96/0.77  fof(f42,plain,(
% 2.96/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.96/0.77    inference(nnf_transformation,[],[f1])).
% 2.96/0.77  fof(f1,axiom,(
% 2.96/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.96/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.96/0.77  fof(f122,plain,(
% 2.96/0.77    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.96/0.77    inference(resolution,[],[f72,f61])).
% 2.96/0.77  fof(f837,plain,(
% 2.96/0.77    ( ! [X17] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X17)) )),
% 2.96/0.77    inference(forward_demodulation,[],[f835,f157])).
% 2.96/0.77  fof(f835,plain,(
% 2.96/0.77    ( ! [X17] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X17) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X17,k1_xboole_0)) )),
% 2.96/0.77    inference(resolution,[],[f123,f117])).
% 2.96/0.77  fof(f117,plain,(
% 2.96/0.77    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 2.96/0.77    inference(forward_demodulation,[],[f96,f92])).
% 2.96/0.77  fof(f92,plain,(
% 2.96/0.77    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.96/0.77    inference(equality_resolution,[],[f75])).
% 2.96/0.77  fof(f75,plain,(
% 2.96/0.77    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.96/0.77    inference(cnf_transformation,[],[f46])).
% 2.96/0.77  fof(f46,plain,(
% 2.96/0.77    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.96/0.77    inference(flattening,[],[f45])).
% 2.96/0.77  fof(f45,plain,(
% 2.96/0.77    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.96/0.77    inference(nnf_transformation,[],[f2])).
% 2.96/0.77  fof(f2,axiom,(
% 2.96/0.77    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.96/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.96/0.77  fof(f96,plain,(
% 2.96/0.77    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.96/0.77    inference(equality_resolution,[],[f82])).
% 2.96/0.77  fof(f82,plain,(
% 2.96/0.77    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.96/0.77    inference(cnf_transformation,[],[f47])).
% 2.96/0.77  fof(f47,plain,(
% 2.96/0.77    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.77    inference(nnf_transformation,[],[f32])).
% 2.96/0.77  fof(f32,plain,(
% 2.96/0.77    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.77    inference(flattening,[],[f31])).
% 2.96/0.77  fof(f31,plain,(
% 2.96/0.77    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.77    inference(ennf_transformation,[],[f8])).
% 2.96/0.77  fof(f8,axiom,(
% 2.96/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.96/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.96/0.77  fof(f123,plain,(
% 2.96/0.77    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.96/0.77    inference(resolution,[],[f73,f89])).
% 2.96/0.77  fof(f89,plain,(
% 2.96/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.96/0.77    inference(equality_resolution,[],[f70])).
% 2.96/0.77  fof(f70,plain,(
% 2.96/0.77    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.96/0.77    inference(cnf_transformation,[],[f43])).
% 2.96/0.77  fof(f73,plain,(
% 2.96/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.96/0.77    inference(cnf_transformation,[],[f44])).
% 2.96/0.77  fof(f4043,plain,(
% 2.96/0.77    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_1 | ~spl4_12 | ~spl4_13 | ~spl4_23 | ~spl4_30 | ~spl4_73)),
% 2.96/0.77    inference(forward_demodulation,[],[f4042,f1612])).
% 2.96/0.77  fof(f4042,plain,(
% 2.96/0.77    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl4_1 | ~spl4_12 | ~spl4_13 | ~spl4_23 | ~spl4_30 | ~spl4_73)),
% 2.96/0.77    inference(forward_demodulation,[],[f4041,f661])).
% 2.96/0.77  fof(f661,plain,(
% 2.96/0.77    k1_xboole_0 = sK2 | ~spl4_30),
% 2.96/0.77    inference(avatar_component_clause,[],[f659])).
% 2.96/0.77  fof(f659,plain,(
% 2.96/0.77    spl4_30 <=> k1_xboole_0 = sK2),
% 2.96/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.96/0.77  fof(f4041,plain,(
% 2.96/0.77    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (spl4_1 | ~spl4_12 | ~spl4_13 | ~spl4_23 | ~spl4_73)),
% 2.96/0.77    inference(forward_demodulation,[],[f4040,f205])).
% 2.96/0.77  fof(f205,plain,(
% 2.96/0.77    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl4_12),
% 2.96/0.77    inference(avatar_component_clause,[],[f203])).
% 2.96/0.77  fof(f203,plain,(
% 2.96/0.77    spl4_12 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 2.96/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.96/0.77  fof(f4040,plain,(
% 2.96/0.77    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (spl4_1 | ~spl4_13 | ~spl4_23 | ~spl4_73)),
% 2.96/0.77    inference(subsumption_resolution,[],[f4039,f48])).
% 2.96/0.77  fof(f48,plain,(
% 2.96/0.77    v2_pre_topc(sK0)),
% 2.96/0.77    inference(cnf_transformation,[],[f39])).
% 2.96/0.77  fof(f39,plain,(
% 2.96/0.77    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.96/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37,f36,f35])).
% 2.96/0.77  fof(f35,plain,(
% 2.96/0.77    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.96/0.77    introduced(choice_axiom,[])).
% 3.27/0.77  fof(f36,plain,(
% 3.27/0.77    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.27/0.77    introduced(choice_axiom,[])).
% 3.27/0.77  fof(f37,plain,(
% 3.27/0.77    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 3.27/0.77    introduced(choice_axiom,[])).
% 3.27/0.77  fof(f38,plain,(
% 3.27/0.77    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 3.27/0.77    introduced(choice_axiom,[])).
% 3.27/0.77  fof(f34,plain,(
% 3.27/0.77    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.27/0.77    inference(flattening,[],[f33])).
% 3.27/0.77  fof(f33,plain,(
% 3.27/0.77    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.27/0.77    inference(nnf_transformation,[],[f20])).
% 3.27/0.77  fof(f20,plain,(
% 3.27/0.77    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.27/0.77    inference(flattening,[],[f19])).
% 3.27/0.77  fof(f19,plain,(
% 3.27/0.77    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.27/0.77    inference(ennf_transformation,[],[f15])).
% 3.27/0.77  fof(f15,negated_conjecture,(
% 3.27/0.77    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.27/0.77    inference(negated_conjecture,[],[f14])).
% 3.27/0.77  fof(f14,conjecture,(
% 3.27/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.27/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 3.27/0.77  fof(f4039,plain,(
% 3.27/0.77    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_13 | ~spl4_23 | ~spl4_73)),
% 3.27/0.77    inference(subsumption_resolution,[],[f4038,f49])).
% 3.27/0.77  fof(f49,plain,(
% 3.27/0.77    l1_pre_topc(sK0)),
% 3.27/0.77    inference(cnf_transformation,[],[f39])).
% 3.27/0.77  fof(f4038,plain,(
% 3.27/0.77    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_13 | ~spl4_23 | ~spl4_73)),
% 3.27/0.77    inference(subsumption_resolution,[],[f4037,f53])).
% 3.27/0.77  fof(f53,plain,(
% 3.27/0.77    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.27/0.77    inference(cnf_transformation,[],[f39])).
% 3.27/0.77  fof(f4037,plain,(
% 3.27/0.77    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_13 | ~spl4_23 | ~spl4_73)),
% 3.27/0.77    inference(subsumption_resolution,[],[f4036,f54])).
% 3.27/0.77  fof(f54,plain,(
% 3.27/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.27/0.77    inference(cnf_transformation,[],[f39])).
% 3.27/0.77  fof(f4036,plain,(
% 3.27/0.77    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_13 | ~spl4_23 | ~spl4_73)),
% 3.27/0.77    inference(subsumption_resolution,[],[f4035,f114])).
% 3.27/0.77  fof(f114,plain,(
% 3.27/0.77    v1_funct_1(sK2)),
% 3.27/0.77    inference(forward_demodulation,[],[f55,f58])).
% 3.27/0.77  fof(f58,plain,(
% 3.27/0.77    sK2 = sK3),
% 3.27/0.77    inference(cnf_transformation,[],[f39])).
% 3.27/0.77  fof(f55,plain,(
% 3.27/0.77    v1_funct_1(sK3)),
% 3.27/0.77    inference(cnf_transformation,[],[f39])).
% 3.27/0.77  fof(f4035,plain,(
% 3.27/0.77    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_13 | ~spl4_23 | ~spl4_73)),
% 3.27/0.77    inference(subsumption_resolution,[],[f4034,f105])).
% 3.27/0.77  fof(f105,plain,(
% 3.27/0.77    ~v5_pre_topc(sK2,sK0,sK1) | spl4_1),
% 3.27/0.77    inference(avatar_component_clause,[],[f103])).
% 3.27/0.77  fof(f103,plain,(
% 3.27/0.77    spl4_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 3.27/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.27/0.77  fof(f4034,plain,(
% 3.27/0.77    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_13 | ~spl4_23 | ~spl4_73)),
% 3.27/0.77    inference(subsumption_resolution,[],[f4033,f2950])).
% 3.27/0.77  fof(f2950,plain,(
% 3.27/0.77    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_73),
% 3.27/0.77    inference(avatar_component_clause,[],[f2949])).
% 3.27/0.77  fof(f2949,plain,(
% 3.27/0.77    spl4_73 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 3.27/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 3.27/0.77  fof(f4033,plain,(
% 3.27/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_13 | ~spl4_23)),
% 3.27/0.77    inference(resolution,[],[f3603,f509])).
% 3.27/0.77  fof(f509,plain,(
% 3.27/0.77    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_23),
% 3.27/0.77    inference(avatar_component_clause,[],[f507])).
% 3.27/0.77  fof(f507,plain,(
% 3.27/0.77    spl4_23 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.27/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 3.27/0.77  fof(f3603,plain,(
% 3.27/0.77    ( ! [X6,X7] : (~v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_13),
% 3.27/0.77    inference(forward_demodulation,[],[f3602,f91])).
% 3.27/0.77  fof(f91,plain,(
% 3.27/0.77    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.27/0.77    inference(equality_resolution,[],[f76])).
% 3.27/0.77  fof(f76,plain,(
% 3.27/0.77    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.27/0.77    inference(cnf_transformation,[],[f46])).
% 3.27/0.77  fof(f3602,plain,(
% 3.27/0.77    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_13),
% 3.27/0.77    inference(subsumption_resolution,[],[f3601,f50])).
% 3.27/0.77  fof(f50,plain,(
% 3.27/0.77    v2_pre_topc(sK1)),
% 3.27/0.77    inference(cnf_transformation,[],[f39])).
% 3.27/0.77  fof(f3601,plain,(
% 3.27/0.77    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_13),
% 3.27/0.77    inference(subsumption_resolution,[],[f3563,f51])).
% 3.27/0.77  fof(f51,plain,(
% 3.27/0.77    l1_pre_topc(sK1)),
% 3.27/0.77    inference(cnf_transformation,[],[f39])).
% 3.27/0.77  fof(f3563,plain,(
% 3.27/0.77    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_13),
% 3.27/0.77    inference(superposition,[],[f101,f212])).
% 3.27/0.77  fof(f212,plain,(
% 3.27/0.77    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_13),
% 3.27/0.77    inference(avatar_component_clause,[],[f210])).
% 3.27/0.77  fof(f210,plain,(
% 3.27/0.77    spl4_13 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.27/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 3.27/0.77  fof(f101,plain,(
% 3.27/0.77    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.77    inference(duplicate_literal_removal,[],[f85])).
% 3.27/0.77  fof(f85,plain,(
% 3.27/0.77    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.77    inference(equality_resolution,[],[f65])).
% 3.27/0.77  fof(f65,plain,(
% 3.27/0.77    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.77    inference(cnf_transformation,[],[f40])).
% 3.27/0.77  fof(f40,plain,(
% 3.27/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/0.77    inference(nnf_transformation,[],[f25])).
% 3.27/0.77  fof(f25,plain,(
% 3.27/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/0.77    inference(flattening,[],[f24])).
% 3.27/0.77  fof(f24,plain,(
% 3.27/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.27/0.77    inference(ennf_transformation,[],[f13])).
% 3.27/0.77  fof(f13,axiom,(
% 3.27/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.27/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 3.27/0.77  fof(f3416,plain,(
% 3.27/0.77    ~spl4_12 | ~spl4_13 | spl4_14 | spl4_73),
% 3.27/0.77    inference(avatar_contradiction_clause,[],[f3415])).
% 3.27/0.77  fof(f3415,plain,(
% 3.27/0.77    $false | (~spl4_12 | ~spl4_13 | spl4_14 | spl4_73)),
% 3.27/0.77    inference(global_subsumption,[],[f602,f2951])).
% 3.27/0.77  fof(f2951,plain,(
% 3.27/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl4_73),
% 3.27/0.77    inference(avatar_component_clause,[],[f2949])).
% 3.27/0.77  fof(f602,plain,(
% 3.27/0.77    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_13),
% 3.27/0.77    inference(forward_demodulation,[],[f588,f91])).
% 3.27/0.77  fof(f588,plain,(
% 3.27/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~spl4_13),
% 3.27/0.77    inference(superposition,[],[f112,f212])).
% 3.27/0.77  fof(f112,plain,(
% 3.27/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.27/0.77    inference(forward_demodulation,[],[f57,f58])).
% 3.27/0.77  fof(f57,plain,(
% 3.27/0.77    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.27/0.77    inference(cnf_transformation,[],[f39])).
% 3.27/0.77  fof(f3327,plain,(
% 3.27/0.77    spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_17 | ~spl4_24 | ~spl4_25),
% 3.27/0.77    inference(avatar_contradiction_clause,[],[f3326])).
% 3.27/0.77  fof(f3326,plain,(
% 3.27/0.77    $false | (spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_17 | ~spl4_24 | ~spl4_25)),
% 3.27/0.77    inference(subsumption_resolution,[],[f3325,f50])).
% 3.27/0.77  fof(f3325,plain,(
% 3.27/0.77    ~v2_pre_topc(sK1) | (spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_17 | ~spl4_24 | ~spl4_25)),
% 3.27/0.77    inference(subsumption_resolution,[],[f3324,f51])).
% 3.27/0.77  fof(f3324,plain,(
% 3.27/0.77    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_17 | ~spl4_24 | ~spl4_25)),
% 3.27/0.77    inference(subsumption_resolution,[],[f3323,f114])).
% 3.27/0.77  fof(f3323,plain,(
% 3.27/0.77    ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_17 | ~spl4_24 | ~spl4_25)),
% 3.27/0.77    inference(subsumption_resolution,[],[f3322,f105])).
% 3.27/0.77  fof(f3322,plain,(
% 3.27/0.77    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_12 | ~spl4_14 | ~spl4_17 | ~spl4_24 | ~spl4_25)),
% 3.27/0.77    inference(subsumption_resolution,[],[f3321,f520])).
% 3.27/0.77  fof(f520,plain,(
% 3.27/0.77    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl4_25),
% 3.27/0.77    inference(avatar_component_clause,[],[f519])).
% 3.27/0.77  fof(f519,plain,(
% 3.27/0.77    spl4_25 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 3.27/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 3.27/0.77  fof(f3321,plain,(
% 3.27/0.77    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_12 | ~spl4_14 | ~spl4_17 | ~spl4_24)),
% 3.27/0.77    inference(subsumption_resolution,[],[f3319,f516])).
% 3.27/0.77  fof(f516,plain,(
% 3.27/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl4_24),
% 3.27/0.77    inference(avatar_component_clause,[],[f515])).
% 3.27/0.77  fof(f515,plain,(
% 3.27/0.77    spl4_24 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 3.27/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 3.27/0.77  fof(f3319,plain,(
% 3.27/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_12 | ~spl4_14 | ~spl4_17)),
% 3.27/0.77    inference(resolution,[],[f2901,f3270])).
% 3.27/0.77  fof(f3270,plain,(
% 3.27/0.77    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl4_12 | ~spl4_17)),
% 3.27/0.77    inference(forward_demodulation,[],[f310,f205])).
% 3.27/0.77  fof(f310,plain,(
% 3.27/0.77    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl4_17),
% 3.27/0.77    inference(avatar_component_clause,[],[f308])).
% 3.27/0.77  fof(f308,plain,(
% 3.27/0.77    spl4_17 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 3.27/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 3.27/0.77  fof(f2901,plain,(
% 3.27/0.77    ( ! [X4,X5] : (~v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | ~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_12 | ~spl4_14)),
% 3.27/0.77    inference(duplicate_literal_removal,[],[f2900])).
% 3.27/0.77  fof(f2900,plain,(
% 3.27/0.77    ( ! [X4,X5] : (~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | ~v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_12 | ~spl4_14)),
% 3.27/0.77    inference(forward_demodulation,[],[f2899,f2821])).
% 3.27/0.77  fof(f2821,plain,(
% 3.27/0.77    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl4_12 | ~spl4_14)),
% 3.27/0.77    inference(forward_demodulation,[],[f216,f205])).
% 3.27/0.77  fof(f216,plain,(
% 3.27/0.77    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | ~spl4_14),
% 3.27/0.77    inference(avatar_component_clause,[],[f214])).
% 3.27/0.77  fof(f214,plain,(
% 3.27/0.77    spl4_14 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)),
% 3.27/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.27/0.78  fof(f2899,plain,(
% 3.27/0.78    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | ~v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_12 | ~spl4_14)),
% 3.27/0.78    inference(duplicate_literal_removal,[],[f2898])).
% 3.27/0.78  fof(f2898,plain,(
% 3.27/0.78    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | ~v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | ~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_12 | ~spl4_14)),
% 3.27/0.78    inference(forward_demodulation,[],[f2897,f2821])).
% 3.27/0.78  fof(f2897,plain,(
% 3.27/0.78    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5)))) | ~v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | ~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | ~spl4_12),
% 3.27/0.78    inference(subsumption_resolution,[],[f2896,f48])).
% 3.27/0.78  fof(f2896,plain,(
% 3.27/0.78    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5)))) | ~v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | ~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~v2_pre_topc(sK0)) ) | ~spl4_12),
% 3.27/0.78    inference(subsumption_resolution,[],[f2869,f49])).
% 3.27/0.78  fof(f2869,plain,(
% 3.27/0.78    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5)))) | ~v5_pre_topc(X4,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X5) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_2(X4,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | ~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_12),
% 3.27/0.78    inference(superposition,[],[f99,f205])).
% 3.27/0.78  fof(f99,plain,(
% 3.27/0.78    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(duplicate_literal_removal,[],[f87])).
% 3.27/0.78  fof(f87,plain,(
% 3.27/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(equality_resolution,[],[f67])).
% 3.27/0.78  fof(f67,plain,(
% 3.27/0.78    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(cnf_transformation,[],[f41])).
% 3.27/0.78  fof(f41,plain,(
% 3.27/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/0.78    inference(nnf_transformation,[],[f27])).
% 3.27/0.78  fof(f27,plain,(
% 3.27/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/0.78    inference(flattening,[],[f26])).
% 3.27/0.78  fof(f26,plain,(
% 3.27/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.27/0.78    inference(ennf_transformation,[],[f12])).
% 3.27/0.78  fof(f12,axiom,(
% 3.27/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.27/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 3.27/0.78  fof(f3288,plain,(
% 3.27/0.78    ~spl4_1 | spl4_2 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f3287])).
% 3.27/0.78  fof(f3287,plain,(
% 3.27/0.78    $false | (~spl4_1 | spl4_2 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3286,f520])).
% 3.27/0.78  fof(f3286,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl4_1 | spl4_2 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(forward_demodulation,[],[f3285,f2821])).
% 3.27/0.78  fof(f3285,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_1 | spl4_2 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(forward_demodulation,[],[f3284,f205])).
% 3.27/0.78  fof(f3284,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_1 | spl4_2 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3283,f516])).
% 3.27/0.78  fof(f3283,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_1 | spl4_2 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(forward_demodulation,[],[f3265,f2821])).
% 3.27/0.78  fof(f3265,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_1 | spl4_2 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(forward_demodulation,[],[f3264,f205])).
% 3.27/0.78  fof(f3264,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_1 | spl4_2 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3263,f3259])).
% 3.27/0.78  fof(f3259,plain,(
% 3.27/0.78    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3258,f50])).
% 3.27/0.78  fof(f3258,plain,(
% 3.27/0.78    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3257,f51])).
% 3.27/0.78  fof(f3257,plain,(
% 3.27/0.78    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3245,f114])).
% 3.27/0.78  fof(f3245,plain,(
% 3.27/0.78    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3244,f104])).
% 3.27/0.78  fof(f104,plain,(
% 3.27/0.78    v5_pre_topc(sK2,sK0,sK1) | ~spl4_1),
% 3.27/0.78    inference(avatar_component_clause,[],[f103])).
% 3.27/0.78  fof(f3244,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_25)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3225,f520])).
% 3.27/0.78  fof(f3225,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_12 | ~spl4_14 | ~spl4_24)),
% 3.27/0.78    inference(resolution,[],[f2893,f516])).
% 3.27/0.78  fof(f2893,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl4_12 | ~spl4_14)),
% 3.27/0.78    inference(duplicate_literal_removal,[],[f2892])).
% 3.27/0.78  fof(f2892,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl4_12 | ~spl4_14)),
% 3.27/0.78    inference(forward_demodulation,[],[f2891,f2821])).
% 3.27/0.78  fof(f2891,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl4_12 | ~spl4_14)),
% 3.27/0.78    inference(duplicate_literal_removal,[],[f2890])).
% 3.27/0.78  fof(f2890,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl4_12 | ~spl4_14)),
% 3.27/0.78    inference(forward_demodulation,[],[f2889,f2821])).
% 3.27/0.78  fof(f2889,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl4_12),
% 3.27/0.78    inference(subsumption_resolution,[],[f2888,f48])).
% 3.27/0.78  fof(f2888,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~v2_pre_topc(sK0)) ) | ~spl4_12),
% 3.27/0.78    inference(subsumption_resolution,[],[f2867,f49])).
% 3.27/0.78  fof(f2867,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_12),
% 3.27/0.78    inference(superposition,[],[f98,f205])).
% 3.27/0.78  fof(f98,plain,(
% 3.27/0.78    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(duplicate_literal_removal,[],[f88])).
% 3.27/0.78  fof(f88,plain,(
% 3.27/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(equality_resolution,[],[f66])).
% 3.27/0.78  fof(f66,plain,(
% 3.27/0.78    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(cnf_transformation,[],[f41])).
% 3.27/0.78  fof(f3263,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl4_2 | ~spl4_12)),
% 3.27/0.78    inference(forward_demodulation,[],[f3262,f205])).
% 3.27/0.78  fof(f3262,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl4_2),
% 3.27/0.78    inference(subsumption_resolution,[],[f1911,f2491])).
% 3.27/0.78  fof(f2491,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_2),
% 3.27/0.78    inference(forward_demodulation,[],[f109,f58])).
% 3.27/0.78  fof(f109,plain,(
% 3.27/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_2),
% 3.27/0.78    inference(avatar_component_clause,[],[f107])).
% 3.27/0.78  fof(f107,plain,(
% 3.27/0.78    spl4_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.27/0.78  fof(f1911,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 3.27/0.78    inference(subsumption_resolution,[],[f1910,f141])).
% 3.27/0.78  fof(f141,plain,(
% 3.27/0.78    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(subsumption_resolution,[],[f139,f49])).
% 3.27/0.78  fof(f139,plain,(
% 3.27/0.78    ~l1_pre_topc(sK0) | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(resolution,[],[f63,f48])).
% 3.27/0.78  fof(f63,plain,(
% 3.27/0.78    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 3.27/0.78    inference(cnf_transformation,[],[f23])).
% 3.27/0.78  fof(f23,plain,(
% 3.27/0.78    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/0.78    inference(flattening,[],[f22])).
% 3.27/0.78  fof(f22,plain,(
% 3.27/0.78    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.27/0.78    inference(ennf_transformation,[],[f16])).
% 3.27/0.78  fof(f16,plain,(
% 3.27/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.27/0.78    inference(pure_predicate_removal,[],[f11])).
% 3.27/0.78  fof(f11,axiom,(
% 3.27/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.27/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 3.27/0.78  fof(f1910,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(subsumption_resolution,[],[f1909,f292])).
% 3.27/0.78  fof(f292,plain,(
% 3.27/0.78    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(resolution,[],[f125,f68])).
% 3.27/0.78  fof(f68,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 3.27/0.78    inference(cnf_transformation,[],[f28])).
% 3.27/0.78  fof(f28,plain,(
% 3.27/0.78    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.27/0.78    inference(ennf_transformation,[],[f17])).
% 3.27/0.78  fof(f17,plain,(
% 3.27/0.78    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.27/0.78    inference(pure_predicate_removal,[],[f9])).
% 3.27/0.78  fof(f9,axiom,(
% 3.27/0.78    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.27/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 3.27/0.78  fof(f125,plain,(
% 3.27/0.78    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.27/0.78    inference(resolution,[],[f62,f49])).
% 3.27/0.78  fof(f62,plain,(
% 3.27/0.78    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.27/0.78    inference(cnf_transformation,[],[f21])).
% 3.27/0.78  fof(f21,plain,(
% 3.27/0.78    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.27/0.78    inference(ennf_transformation,[],[f10])).
% 3.27/0.78  fof(f10,axiom,(
% 3.27/0.78    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.27/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 3.27/0.78  fof(f1909,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(subsumption_resolution,[],[f1908,f50])).
% 3.27/0.78  fof(f1908,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(subsumption_resolution,[],[f1907,f51])).
% 3.27/0.78  fof(f1907,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(subsumption_resolution,[],[f1906,f114])).
% 3.27/0.78  fof(f1906,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(subsumption_resolution,[],[f238,f113])).
% 3.27/0.78  fof(f113,plain,(
% 3.27/0.78    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.27/0.78    inference(forward_demodulation,[],[f56,f58])).
% 3.27/0.78  fof(f56,plain,(
% 3.27/0.78    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.27/0.78    inference(cnf_transformation,[],[f39])).
% 3.27/0.78  fof(f238,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.78    inference(resolution,[],[f100,f112])).
% 3.27/0.78  fof(f100,plain,(
% 3.27/0.78    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(duplicate_literal_removal,[],[f86])).
% 3.27/0.78  fof(f86,plain,(
% 3.27/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(equality_resolution,[],[f64])).
% 3.27/0.78  fof(f64,plain,(
% 3.27/0.78    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(cnf_transformation,[],[f40])).
% 3.27/0.78  fof(f2809,plain,(
% 3.27/0.78    spl4_15 | ~spl4_30),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f2808])).
% 3.27/0.78  fof(f2808,plain,(
% 3.27/0.78    $false | (spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(global_subsumption,[],[f1421,f231])).
% 3.27/0.78  fof(f231,plain,(
% 3.27/0.78    ~v1_funct_1(k1_xboole_0) | spl4_15),
% 3.27/0.78    inference(avatar_component_clause,[],[f229])).
% 3.27/0.78  fof(f229,plain,(
% 3.27/0.78    spl4_15 <=> v1_funct_1(k1_xboole_0)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 3.27/0.78  fof(f1421,plain,(
% 3.27/0.78    v1_funct_1(k1_xboole_0) | ~spl4_30),
% 3.27/0.78    inference(superposition,[],[f114,f661])).
% 3.27/0.78  fof(f2786,plain,(
% 3.27/0.78    ~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f2785])).
% 3.27/0.78  fof(f2785,plain,(
% 3.27/0.78    $false | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2784,f1615])).
% 3.27/0.78  fof(f2784,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2783,f661])).
% 3.27/0.78  fof(f2783,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2782,f2486])).
% 3.27/0.78  fof(f2486,plain,(
% 3.27/0.78    k1_xboole_0 = u1_struct_0(sK0) | (~spl4_12 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2485,f1612])).
% 3.27/0.78  fof(f2485,plain,(
% 3.27/0.78    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | (~spl4_12 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f205,f661])).
% 3.27/0.78  fof(f2782,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2781,f61])).
% 3.27/0.78  fof(f2781,plain,(
% 3.27/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2780,f661])).
% 3.27/0.78  fof(f2780,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2779,f92])).
% 3.27/0.78  fof(f2779,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2778,f2486])).
% 3.27/0.78  fof(f2778,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2777,f2555])).
% 3.27/0.78  fof(f2555,plain,(
% 3.27/0.78    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl4_2 | ~spl4_12 | ~spl4_30)),
% 3.27/0.78    inference(superposition,[],[f2492,f2486])).
% 3.27/0.78  fof(f2492,plain,(
% 3.27/0.78    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl4_2 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2491,f661])).
% 3.27/0.78  fof(f2777,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2776,f661])).
% 3.27/0.78  fof(f2776,plain,(
% 3.27/0.78    v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2775,f2486])).
% 3.27/0.78  fof(f2775,plain,(
% 3.27/0.78    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2429,f2774])).
% 3.27/0.78  fof(f2774,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2773,f50])).
% 3.27/0.78  fof(f2773,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2768,f51])).
% 3.27/0.78  fof(f2768,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(resolution,[],[f2653,f2495])).
% 3.27/0.78  fof(f2495,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl4_1 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f104,f661])).
% 3.27/0.78  fof(f2653,plain,(
% 3.27/0.78    ( ! [X22] : (~v5_pre_topc(k1_xboole_0,sK0,X22) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22))) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22)) ) | (~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2652,f48])).
% 3.27/0.78  fof(f2652,plain,(
% 3.27/0.78    ( ! [X22] : (v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22))) | ~v5_pre_topc(k1_xboole_0,sK0,X22) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | ~v2_pre_topc(sK0)) ) | (~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2651,f49])).
% 3.27/0.78  fof(f2651,plain,(
% 3.27/0.78    ( ! [X22] : (v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22))) | ~v5_pre_topc(k1_xboole_0,sK0,X22) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2650,f1615])).
% 3.27/0.78  fof(f2650,plain,(
% 3.27/0.78    ( ! [X22] : (v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22))) | ~v5_pre_topc(k1_xboole_0,sK0,X22) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X22)) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2568,f1615])).
% 3.27/0.78  fof(f2568,plain,(
% 3.27/0.78    ( ! [X22] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22))) | ~v5_pre_topc(k1_xboole_0,sK0,X22) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X22)) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_12 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(superposition,[],[f715,f2486])).
% 3.27/0.78  fof(f715,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_15),
% 3.27/0.78    inference(subsumption_resolution,[],[f693,f230])).
% 3.27/0.78  fof(f230,plain,(
% 3.27/0.78    v1_funct_1(k1_xboole_0) | ~spl4_15),
% 3.27/0.78    inference(avatar_component_clause,[],[f229])).
% 3.27/0.78  fof(f693,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(subsumption_resolution,[],[f239,f61])).
% 3.27/0.78  fof(f239,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(resolution,[],[f100,f61])).
% 3.27/0.78  fof(f2429,plain,(
% 3.27/0.78    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_10 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2135,f661])).
% 3.27/0.78  fof(f2135,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_10),
% 3.27/0.78    inference(subsumption_resolution,[],[f2134,f48])).
% 3.27/0.78  fof(f2134,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~spl4_10),
% 3.27/0.78    inference(subsumption_resolution,[],[f2133,f49])).
% 3.27/0.78  fof(f2133,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_10),
% 3.27/0.78    inference(subsumption_resolution,[],[f2132,f142])).
% 3.27/0.78  fof(f142,plain,(
% 3.27/0.78    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.27/0.78    inference(subsumption_resolution,[],[f140,f51])).
% 3.27/0.78  fof(f140,plain,(
% 3.27/0.78    ~l1_pre_topc(sK1) | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.27/0.78    inference(resolution,[],[f63,f50])).
% 3.27/0.78  fof(f2132,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_10),
% 3.27/0.78    inference(subsumption_resolution,[],[f2131,f188])).
% 3.27/0.78  fof(f188,plain,(
% 3.27/0.78    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_10),
% 3.27/0.78    inference(avatar_component_clause,[],[f187])).
% 3.27/0.78  fof(f187,plain,(
% 3.27/0.78    spl4_10 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.27/0.78  fof(f2131,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2130,f114])).
% 3.27/0.78  fof(f2130,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.27/0.78    inference(subsumption_resolution,[],[f225,f113])).
% 3.27/0.78  fof(f225,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.27/0.78    inference(resolution,[],[f98,f112])).
% 3.27/0.78  fof(f2676,plain,(
% 3.27/0.78    ~spl4_12 | spl4_21 | ~spl4_30),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f2675])).
% 3.27/0.78  fof(f2675,plain,(
% 3.27/0.78    $false | (~spl4_12 | spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2674,f1615])).
% 3.27/0.78  fof(f2674,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_12 | spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(superposition,[],[f2420,f2486])).
% 3.27/0.78  fof(f2420,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f501,f661])).
% 3.27/0.78  fof(f501,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl4_21),
% 3.27/0.78    inference(avatar_component_clause,[],[f499])).
% 3.27/0.78  fof(f499,plain,(
% 3.27/0.78    spl4_21 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 3.27/0.78  fof(f2415,plain,(
% 3.27/0.78    spl4_1 | ~spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_30),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f2414])).
% 3.27/0.78  fof(f2414,plain,(
% 3.27/0.78    $false | (spl4_1 | ~spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2413,f1339])).
% 3.27/0.78  fof(f1339,plain,(
% 3.27/0.78    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f1305,f661])).
% 3.27/0.78  fof(f1305,plain,(
% 3.27/0.78    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl4_11),
% 3.27/0.78    inference(superposition,[],[f53,f201])).
% 3.27/0.78  fof(f201,plain,(
% 3.27/0.78    k1_xboole_0 = u1_struct_0(sK1) | ~spl4_11),
% 3.27/0.78    inference(avatar_component_clause,[],[f199])).
% 3.27/0.78  fof(f199,plain,(
% 3.27/0.78    spl4_11 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 3.27/0.78  fof(f2413,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (spl4_1 | ~spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2412,f201])).
% 3.27/0.78  fof(f2412,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl4_1 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2411,f50])).
% 3.27/0.78  fof(f2411,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | (spl4_1 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2410,f51])).
% 3.27/0.78  fof(f2410,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl4_1 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2409,f2184])).
% 3.27/0.78  fof(f2184,plain,(
% 3.27/0.78    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl4_1 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f105,f661])).
% 3.27/0.78  fof(f2409,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 3.27/0.78    inference(resolution,[],[f2327,f2180])).
% 3.27/0.78  fof(f2180,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_17 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f310,f661])).
% 3.27/0.78  fof(f2327,plain,(
% 3.27/0.78    ( ! [X9] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X9) | v5_pre_topc(k1_xboole_0,sK0,X9) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl4_14 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2326,f48])).
% 3.27/0.78  fof(f2326,plain,(
% 3.27/0.78    ( ! [X9] : (v5_pre_topc(k1_xboole_0,sK0,X9) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X9) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~v2_pre_topc(sK0)) ) | (~spl4_14 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2325,f49])).
% 3.27/0.78  fof(f2325,plain,(
% 3.27/0.78    ( ! [X9] : (v5_pre_topc(k1_xboole_0,sK0,X9) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X9) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_14 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2278,f1615])).
% 3.27/0.78  fof(f2278,plain,(
% 3.27/0.78    ( ! [X9] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X9)) | v5_pre_topc(k1_xboole_0,sK0,X9) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X9) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_14 | ~spl4_15 | ~spl4_30)),
% 3.27/0.78    inference(superposition,[],[f714,f2243])).
% 3.27/0.78  fof(f2243,plain,(
% 3.27/0.78    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_14 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2242,f1612])).
% 3.27/0.78  fof(f2242,plain,(
% 3.27/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | (~spl4_14 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f216,f661])).
% 3.27/0.78  fof(f714,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_15),
% 3.27/0.78    inference(subsumption_resolution,[],[f696,f230])).
% 3.27/0.78  fof(f696,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(subsumption_resolution,[],[f237,f61])).
% 3.27/0.78  fof(f237,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(resolution,[],[f99,f61])).
% 3.27/0.78  fof(f2230,plain,(
% 3.27/0.78    spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f2229])).
% 3.27/0.78  fof(f2229,plain,(
% 3.27/0.78    $false | (spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2228,f48])).
% 3.27/0.78  fof(f2228,plain,(
% 3.27/0.78    ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2227,f49])).
% 3.27/0.78  fof(f2227,plain,(
% 3.27/0.78    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2226,f1339])).
% 3.27/0.78  fof(f2226,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2200,f2214])).
% 3.27/0.78  fof(f2214,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2213,f1958])).
% 3.27/0.78  fof(f1958,plain,(
% 3.27/0.78    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl4_11 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f1957,f661])).
% 3.27/0.78  fof(f1957,plain,(
% 3.27/0.78    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl4_11 | ~spl4_21)),
% 3.27/0.78    inference(forward_demodulation,[],[f500,f201])).
% 3.27/0.78  fof(f500,plain,(
% 3.27/0.78    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_21),
% 3.27/0.78    inference(avatar_component_clause,[],[f499])).
% 3.27/0.78  fof(f2213,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2212,f661])).
% 3.27/0.78  fof(f2212,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2211,f201])).
% 3.27/0.78  fof(f2211,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2210,f61])).
% 3.27/0.78  fof(f2210,plain,(
% 3.27/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2209,f661])).
% 3.27/0.78  fof(f2209,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2208,f201])).
% 3.27/0.78  fof(f2208,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2207,f661])).
% 3.27/0.78  fof(f2207,plain,(
% 3.27/0.78    v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2206,f201])).
% 3.27/0.78  fof(f2206,plain,(
% 3.27/0.78    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2159,f2183])).
% 3.27/0.78  fof(f2183,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_2 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2182,f661])).
% 3.27/0.78  fof(f2182,plain,(
% 3.27/0.78    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_2 | ~spl4_11)),
% 3.27/0.78    inference(forward_demodulation,[],[f2181,f58])).
% 3.27/0.78  fof(f2181,plain,(
% 3.27/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_2 | ~spl4_11)),
% 3.27/0.78    inference(forward_demodulation,[],[f108,f201])).
% 3.27/0.78  fof(f108,plain,(
% 3.27/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_2),
% 3.27/0.78    inference(avatar_component_clause,[],[f107])).
% 3.27/0.78  fof(f2159,plain,(
% 3.27/0.78    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2158,f661])).
% 3.27/0.78  fof(f2158,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_10 | ~spl4_11)),
% 3.27/0.78    inference(forward_demodulation,[],[f2157,f201])).
% 3.27/0.78  fof(f2157,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_10),
% 3.27/0.78    inference(subsumption_resolution,[],[f2156,f48])).
% 3.27/0.78  fof(f2156,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~spl4_10),
% 3.27/0.78    inference(subsumption_resolution,[],[f2155,f49])).
% 3.27/0.78  fof(f2155,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_10),
% 3.27/0.78    inference(subsumption_resolution,[],[f2154,f142])).
% 3.27/0.78  fof(f2154,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_10),
% 3.27/0.78    inference(subsumption_resolution,[],[f2153,f188])).
% 3.27/0.78  fof(f2153,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2152,f114])).
% 3.27/0.78  fof(f2152,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.27/0.78    inference(subsumption_resolution,[],[f236,f113])).
% 3.27/0.78  fof(f236,plain,(
% 3.27/0.78    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.27/0.78    inference(resolution,[],[f99,f112])).
% 3.27/0.78  fof(f2200,plain,(
% 3.27/0.78    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2194,f2184])).
% 3.27/0.78  fof(f2194,plain,(
% 3.27/0.78    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(resolution,[],[f1409,f1958])).
% 3.27/0.78  fof(f1409,plain,(
% 3.27/0.78    ( ! [X23] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X23,sK1) | ~v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23)) ) | (~spl4_11 | ~spl4_15)),
% 3.27/0.78    inference(subsumption_resolution,[],[f1408,f50])).
% 3.27/0.78  fof(f1408,plain,(
% 3.27/0.78    ( ! [X23] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X23,sK1) | ~v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23)) ) | (~spl4_11 | ~spl4_15)),
% 3.27/0.78    inference(subsumption_resolution,[],[f1338,f51])).
% 3.27/0.78  fof(f1338,plain,(
% 3.27/0.78    ( ! [X23] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X23,sK1) | ~v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23)) ) | (~spl4_11 | ~spl4_15)),
% 3.27/0.78    inference(superposition,[],[f716,f201])).
% 3.27/0.78  fof(f716,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_15),
% 3.27/0.78    inference(subsumption_resolution,[],[f690,f230])).
% 3.27/0.78  fof(f690,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(subsumption_resolution,[],[f280,f61])).
% 3.27/0.78  fof(f280,plain,(
% 3.27/0.78    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.78    inference(resolution,[],[f101,f61])).
% 3.27/0.78  fof(f2151,plain,(
% 3.27/0.78    ~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f2150])).
% 3.27/0.78  fof(f2150,plain,(
% 3.27/0.78    $false | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2149,f1339])).
% 3.27/0.78  fof(f2149,plain,(
% 3.27/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2148,f661])).
% 3.27/0.78  fof(f2148,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2147,f1963])).
% 3.27/0.78  fof(f1963,plain,(
% 3.27/0.78    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_11 | ~spl4_13)),
% 3.27/0.78    inference(forward_demodulation,[],[f212,f201])).
% 3.27/0.78  fof(f2147,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2146,f201])).
% 3.27/0.78  fof(f2146,plain,(
% 3.27/0.78    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(subsumption_resolution,[],[f2145,f61])).
% 3.27/0.78  fof(f2145,plain,(
% 3.27/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2144,f661])).
% 3.27/0.78  fof(f2144,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2143,f91])).
% 3.27/0.78  fof(f2143,plain,(
% 3.27/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.78    inference(forward_demodulation,[],[f2142,f1963])).
% 3.27/0.79  fof(f2142,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f2141,f201])).
% 3.27/0.79  fof(f2141,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | spl4_2 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f2140,f1936])).
% 3.27/0.79  fof(f1936,plain,(
% 3.27/0.79    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl4_2 | ~spl4_11 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1935,f661])).
% 3.27/0.79  fof(f1935,plain,(
% 3.27/0.79    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl4_2 | ~spl4_11)),
% 3.27/0.79    inference(forward_demodulation,[],[f1934,f58])).
% 3.27/0.79  fof(f1934,plain,(
% 3.27/0.79    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl4_2 | ~spl4_11)),
% 3.27/0.79    inference(forward_demodulation,[],[f109,f201])).
% 3.27/0.79  fof(f2140,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f2139,f661])).
% 3.27/0.79  fof(f2139,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f2138,f201])).
% 3.27/0.79  fof(f2138,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f2137,f2125])).
% 3.27/0.79  fof(f2125,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f2124,f48])).
% 3.27/0.79  fof(f2124,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f2123,f49])).
% 3.27/0.79  fof(f2123,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f2122,f1339])).
% 3.27/0.79  fof(f2122,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f2106,f1937])).
% 3.27/0.79  fof(f1937,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl4_1 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f104,f661])).
% 3.27/0.79  fof(f2106,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30)),
% 3.27/0.79    inference(resolution,[],[f1405,f1958])).
% 3.27/0.79  fof(f1405,plain,(
% 3.27/0.79    ( ! [X21] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X21),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X21,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl4_11 | ~spl4_15)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1404,f50])).
% 3.27/0.79  fof(f1404,plain,(
% 3.27/0.79    ( ! [X21] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X21),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X21,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl4_11 | ~spl4_15)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1336,f51])).
% 3.27/0.79  fof(f1336,plain,(
% 3.27/0.79    ( ! [X21] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X21),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X21,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl4_11 | ~spl4_15)),
% 3.27/0.79    inference(superposition,[],[f715,f201])).
% 3.27/0.79  fof(f2137,plain,(
% 3.27/0.79    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_10 | ~spl4_11 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f2136,f661])).
% 3.27/0.79  fof(f2136,plain,(
% 3.27/0.79    ~v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_10 | ~spl4_11)),
% 3.27/0.79    inference(forward_demodulation,[],[f2135,f201])).
% 3.27/0.79  fof(f1950,plain,(
% 3.27/0.79    spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_18 | ~spl4_30),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f1949])).
% 3.27/0.79  fof(f1949,plain,(
% 3.27/0.79    $false | (spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_18 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1948,f1938])).
% 3.27/0.79  fof(f1938,plain,(
% 3.27/0.79    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_18 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f313,f661])).
% 3.27/0.79  fof(f313,plain,(
% 3.27/0.79    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl4_18),
% 3.27/0.79    inference(avatar_component_clause,[],[f312])).
% 3.27/0.79  fof(f312,plain,(
% 3.27/0.79    spl4_18 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 3.27/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 3.27/0.79  fof(f1948,plain,(
% 3.27/0.79    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1947,f661])).
% 3.27/0.79  fof(f1947,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1946,f201])).
% 3.27/0.79  fof(f1946,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1945,f61])).
% 3.27/0.79  fof(f1945,plain,(
% 3.27/0.79    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1944,f661])).
% 3.27/0.79  fof(f1944,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1943,f91])).
% 3.27/0.79  fof(f1943,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1942,f201])).
% 3.27/0.79  fof(f1942,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl4_2 | ~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1941,f1936])).
% 3.27/0.79  fof(f1941,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1940,f661])).
% 3.27/0.79  fof(f1940,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_11 | ~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1939,f201])).
% 3.27/0.79  fof(f1939,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1912,f1933])).
% 3.27/0.79  fof(f1933,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f310,f661])).
% 3.27/0.79  fof(f1912,plain,(
% 3.27/0.79    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl4_30),
% 3.27/0.79    inference(forward_demodulation,[],[f1911,f661])).
% 3.27/0.79  fof(f1866,plain,(
% 3.27/0.79    ~spl4_14 | spl4_18 | ~spl4_30),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f1865])).
% 3.27/0.79  fof(f1865,plain,(
% 3.27/0.79    $false | (~spl4_14 | spl4_18 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1864,f1615])).
% 3.27/0.79  fof(f1864,plain,(
% 3.27/0.79    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_14 | spl4_18 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1863,f661])).
% 3.27/0.79  fof(f1863,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl4_14 | spl4_18 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1862,f1612])).
% 3.27/0.79  fof(f1862,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl4_14 | spl4_18 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f314,f1297])).
% 3.27/0.79  fof(f1297,plain,(
% 3.27/0.79    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | (~spl4_14 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f216,f661])).
% 3.27/0.79  fof(f314,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | spl4_18),
% 3.27/0.79    inference(avatar_component_clause,[],[f312])).
% 3.27/0.79  fof(f1817,plain,(
% 3.27/0.79    ~spl4_1 | ~spl4_11 | ~spl4_14 | ~spl4_16 | spl4_17 | ~spl4_30),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f1816])).
% 3.27/0.79  fof(f1816,plain,(
% 3.27/0.79    $false | (~spl4_1 | ~spl4_11 | ~spl4_14 | ~spl4_16 | spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1815,f1615])).
% 3.27/0.79  fof(f1815,plain,(
% 3.27/0.79    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_11 | ~spl4_14 | ~spl4_16 | spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(forward_demodulation,[],[f1814,f1612])).
% 3.27/0.79  fof(f1814,plain,(
% 3.27/0.79    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl4_1 | ~spl4_11 | ~spl4_14 | ~spl4_16 | spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1813,f1429])).
% 3.27/0.79  fof(f1429,plain,(
% 3.27/0.79    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl4_17 | ~spl4_30)),
% 3.27/0.79    inference(superposition,[],[f309,f661])).
% 3.27/0.79  fof(f309,plain,(
% 3.27/0.79    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl4_17),
% 3.27/0.79    inference(avatar_component_clause,[],[f308])).
% 3.27/0.79  fof(f1813,plain,(
% 3.27/0.79    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_1 | ~spl4_11 | ~spl4_14 | ~spl4_16 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1802,f1418])).
% 3.27/0.79  fof(f1418,plain,(
% 3.27/0.79    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl4_1 | ~spl4_30)),
% 3.27/0.79    inference(superposition,[],[f104,f661])).
% 3.27/0.79  fof(f1802,plain,(
% 3.27/0.79    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_11 | ~spl4_14 | ~spl4_16 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1801,f51])).
% 3.27/0.79  fof(f1801,plain,(
% 3.27/0.79    ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_11 | ~spl4_14 | ~spl4_16 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1800,f50])).
% 3.27/0.79  fof(f1800,plain,(
% 3.27/0.79    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_11 | ~spl4_14 | ~spl4_16 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1798,f1339])).
% 3.27/0.79  fof(f1798,plain,(
% 3.27/0.79    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_11 | ~spl4_14 | ~spl4_16 | ~spl4_30)),
% 3.27/0.79    inference(superposition,[],[f1492,f201])).
% 3.27/0.79  fof(f1492,plain,(
% 3.27/0.79    ( ! [X8] : (~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X8)) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X8)) | ~v5_pre_topc(k1_xboole_0,sK0,X8) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X8)) ) | (~spl4_14 | ~spl4_16 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1491,f49])).
% 3.27/0.79  fof(f1491,plain,(
% 3.27/0.79    ( ! [X8] : (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X8)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X8)) | ~v5_pre_topc(k1_xboole_0,sK0,X8) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X8)) ) | (~spl4_14 | ~spl4_16 | ~spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f1455,f48])).
% 3.27/0.79  fof(f1455,plain,(
% 3.27/0.79    ( ! [X8] : (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X8)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X8)) | ~v5_pre_topc(k1_xboole_0,sK0,X8) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X8)) ) | (~spl4_14 | ~spl4_16 | ~spl4_30)),
% 3.27/0.79    inference(superposition,[],[f234,f1297])).
% 3.27/0.79  fof(f234,plain,(
% 3.27/0.79    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) ) | ~spl4_16),
% 3.27/0.79    inference(avatar_component_clause,[],[f233])).
% 3.27/0.79  fof(f233,plain,(
% 3.27/0.79    spl4_16 <=> ! [X1,X0] : (~v5_pre_topc(k1_xboole_0,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1))),
% 3.27/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 3.27/0.79  fof(f775,plain,(
% 3.27/0.79    ~spl4_13 | spl4_30),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f774])).
% 3.27/0.79  fof(f774,plain,(
% 3.27/0.79    $false | (~spl4_13 | spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f773,f122])).
% 3.27/0.79  fof(f773,plain,(
% 3.27/0.79    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_13 | spl4_30)),
% 3.27/0.79    inference(subsumption_resolution,[],[f771,f660])).
% 3.27/0.79  fof(f660,plain,(
% 3.27/0.79    k1_xboole_0 != sK2 | spl4_30),
% 3.27/0.79    inference(avatar_component_clause,[],[f659])).
% 3.27/0.79  fof(f771,plain,(
% 3.27/0.79    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl4_13),
% 3.27/0.79    inference(resolution,[],[f649,f71])).
% 3.27/0.79  fof(f649,plain,(
% 3.27/0.79    r1_tarski(sK2,k1_xboole_0) | ~spl4_13),
% 3.27/0.79    inference(resolution,[],[f602,f72])).
% 3.27/0.79  fof(f710,plain,(
% 3.27/0.79    ~spl4_11 | spl4_30),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f709])).
% 3.27/0.79  fof(f709,plain,(
% 3.27/0.79    $false | (~spl4_11 | spl4_30)),
% 3.27/0.79    inference(global_subsumption,[],[f318,f660])).
% 3.27/0.79  fof(f318,plain,(
% 3.27/0.79    k1_xboole_0 = sK2 | ~spl4_11),
% 3.27/0.79    inference(subsumption_resolution,[],[f316,f122])).
% 3.27/0.79  fof(f316,plain,(
% 3.27/0.79    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl4_11),
% 3.27/0.79    inference(resolution,[],[f254,f71])).
% 3.27/0.79  fof(f254,plain,(
% 3.27/0.79    r1_tarski(sK2,k1_xboole_0) | ~spl4_11),
% 3.27/0.79    inference(forward_demodulation,[],[f245,f91])).
% 3.27/0.79  fof(f245,plain,(
% 3.27/0.79    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) | ~spl4_11),
% 3.27/0.79    inference(superposition,[],[f120,f201])).
% 3.27/0.79  fof(f120,plain,(
% 3.27/0.79    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 3.27/0.79    inference(resolution,[],[f72,f54])).
% 3.27/0.79  fof(f698,plain,(
% 3.27/0.79    ~spl4_11 | ~spl4_13 | spl4_21),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f697])).
% 3.27/0.79  fof(f697,plain,(
% 3.27/0.79    $false | (~spl4_11 | ~spl4_13 | spl4_21)),
% 3.27/0.79    inference(global_subsumption,[],[f240,f683])).
% 3.27/0.79  fof(f683,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl4_13 | spl4_21)),
% 3.27/0.79    inference(forward_demodulation,[],[f501,f212])).
% 3.27/0.79  fof(f240,plain,(
% 3.27/0.79    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl4_11),
% 3.27/0.79    inference(superposition,[],[f53,f201])).
% 3.27/0.79  fof(f689,plain,(
% 3.27/0.79    ~spl4_13 | spl4_22),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f688])).
% 3.27/0.79  fof(f688,plain,(
% 3.27/0.79    $false | (~spl4_13 | spl4_22)),
% 3.27/0.79    inference(subsumption_resolution,[],[f687,f602])).
% 3.27/0.79  fof(f687,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_13 | spl4_22)),
% 3.27/0.79    inference(forward_demodulation,[],[f686,f91])).
% 3.27/0.79  fof(f686,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl4_13 | spl4_22)),
% 3.27/0.79    inference(forward_demodulation,[],[f505,f212])).
% 3.27/0.79  fof(f505,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl4_22),
% 3.27/0.79    inference(avatar_component_clause,[],[f503])).
% 3.27/0.79  fof(f503,plain,(
% 3.27/0.79    spl4_22 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.27/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 3.27/0.79  fof(f545,plain,(
% 3.27/0.79    ~spl4_12 | spl4_24),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f544])).
% 3.27/0.79  fof(f544,plain,(
% 3.27/0.79    $false | (~spl4_12 | spl4_24)),
% 3.27/0.79    inference(subsumption_resolution,[],[f526,f517])).
% 3.27/0.79  fof(f517,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | spl4_24),
% 3.27/0.79    inference(avatar_component_clause,[],[f515])).
% 3.27/0.79  fof(f526,plain,(
% 3.27/0.79    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl4_12),
% 3.27/0.79    inference(superposition,[],[f54,f205])).
% 3.27/0.79  fof(f543,plain,(
% 3.27/0.79    ~spl4_12 | spl4_25),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f542])).
% 3.27/0.79  fof(f542,plain,(
% 3.27/0.79    $false | (~spl4_12 | spl4_25)),
% 3.27/0.79    inference(subsumption_resolution,[],[f525,f521])).
% 3.27/0.79  fof(f521,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | spl4_25),
% 3.27/0.79    inference(avatar_component_clause,[],[f519])).
% 3.27/0.79  fof(f525,plain,(
% 3.27/0.79    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl4_12),
% 3.27/0.79    inference(superposition,[],[f53,f205])).
% 3.27/0.79  fof(f522,plain,(
% 3.27/0.79    ~spl4_24 | ~spl4_25 | ~spl4_2 | ~spl4_14 | spl4_17),
% 3.27/0.79    inference(avatar_split_clause,[],[f513,f308,f214,f107,f519,f515])).
% 3.27/0.79  fof(f513,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl4_2 | ~spl4_14 | spl4_17)),
% 3.27/0.79    inference(forward_demodulation,[],[f512,f216])).
% 3.27/0.79  fof(f512,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_2 | ~spl4_14 | spl4_17)),
% 3.27/0.79    inference(forward_demodulation,[],[f511,f216])).
% 3.27/0.79  fof(f511,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_2 | spl4_17)),
% 3.27/0.79    inference(subsumption_resolution,[],[f302,f309])).
% 3.27/0.79  fof(f302,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f301,f141])).
% 3.27/0.79  fof(f301,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f300,f292])).
% 3.27/0.79  fof(f300,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f299,f50])).
% 3.27/0.79  fof(f299,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f298,f51])).
% 3.27/0.79  fof(f298,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f297,f114])).
% 3.27/0.79  fof(f297,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f296,f113])).
% 3.27/0.79  fof(f296,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f279,f119])).
% 3.27/0.79  fof(f119,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_2),
% 3.27/0.79    inference(forward_demodulation,[],[f108,f58])).
% 3.27/0.79  fof(f279,plain,(
% 3.27/0.79    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.27/0.79    inference(resolution,[],[f101,f112])).
% 3.27/0.79  fof(f510,plain,(
% 3.27/0.79    ~spl4_21 | ~spl4_22 | spl4_23 | ~spl4_2 | ~spl4_10),
% 3.27/0.79    inference(avatar_split_clause,[],[f497,f187,f107,f507,f503,f499])).
% 3.27/0.79  fof(f497,plain,(
% 3.27/0.79    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_2 | ~spl4_10)),
% 3.27/0.79    inference(subsumption_resolution,[],[f331,f188])).
% 3.27/0.79  fof(f331,plain,(
% 3.27/0.79    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f330,f48])).
% 3.27/0.79  fof(f330,plain,(
% 3.27/0.79    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f329,f49])).
% 3.27/0.79  fof(f329,plain,(
% 3.27/0.79    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f328,f142])).
% 3.27/0.79  fof(f328,plain,(
% 3.27/0.79    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f327,f114])).
% 3.27/0.79  fof(f327,plain,(
% 3.27/0.79    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f326,f113])).
% 3.27/0.79  fof(f326,plain,(
% 3.27/0.79    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.27/0.79    inference(subsumption_resolution,[],[f236,f119])).
% 3.27/0.79  fof(f495,plain,(
% 3.27/0.79    ~spl4_11 | spl4_15),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f494])).
% 3.27/0.79  fof(f494,plain,(
% 3.27/0.79    $false | (~spl4_11 | spl4_15)),
% 3.27/0.79    inference(subsumption_resolution,[],[f486,f231])).
% 3.27/0.79  fof(f486,plain,(
% 3.27/0.79    v1_funct_1(k1_xboole_0) | ~spl4_11),
% 3.27/0.79    inference(superposition,[],[f114,f318])).
% 3.27/0.79  fof(f323,plain,(
% 3.27/0.79    spl4_10),
% 3.27/0.79    inference(avatar_contradiction_clause,[],[f322])).
% 3.27/0.79  fof(f322,plain,(
% 3.27/0.79    $false | spl4_10),
% 3.27/0.79    inference(subsumption_resolution,[],[f319,f189])).
% 3.27/0.79  fof(f189,plain,(
% 3.27/0.79    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_10),
% 3.27/0.79    inference(avatar_component_clause,[],[f187])).
% 3.27/0.79  fof(f319,plain,(
% 3.27/0.79    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.27/0.79    inference(resolution,[],[f126,f68])).
% 3.27/0.79  fof(f126,plain,(
% 3.27/0.79    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.27/0.79    inference(resolution,[],[f62,f51])).
% 3.27/0.79  fof(f315,plain,(
% 3.27/0.79    spl4_17 | ~spl4_18 | ~spl4_2 | ~spl4_11),
% 3.27/0.79    inference(avatar_split_clause,[],[f306,f199,f107,f312,f308])).
% 3.27/0.79  fof(f306,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_2 | ~spl4_11)),
% 3.27/0.79    inference(forward_demodulation,[],[f305,f201])).
% 3.27/0.79  fof(f305,plain,(
% 3.27/0.79    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_2 | ~spl4_11)),
% 3.27/0.79    inference(subsumption_resolution,[],[f304,f253])).
% 3.27/0.79  fof(f253,plain,(
% 3.27/0.79    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_11),
% 3.27/0.79    inference(forward_demodulation,[],[f241,f91])).
% 3.27/0.79  fof(f241,plain,(
% 3.27/0.79    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl4_11),
% 3.27/0.79    inference(superposition,[],[f54,f201])).
% 3.27/0.79  fof(f304,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_2 | ~spl4_11)),
% 3.27/0.79    inference(forward_demodulation,[],[f303,f91])).
% 3.27/0.79  fof(f303,plain,(
% 3.27/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_2 | ~spl4_11)),
% 3.27/0.79    inference(forward_demodulation,[],[f302,f201])).
% 3.27/0.79  fof(f235,plain,(
% 3.27/0.79    ~spl4_15 | spl4_16),
% 3.27/0.79    inference(avatar_split_clause,[],[f227,f233,f229])).
% 3.27/0.79  fof(f227,plain,(
% 3.27/0.79    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.79    inference(subsumption_resolution,[],[f226,f61])).
% 3.27/0.79  fof(f226,plain,(
% 3.27/0.79    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.79    inference(resolution,[],[f98,f61])).
% 3.27/0.79  fof(f217,plain,(
% 3.27/0.79    spl4_13 | spl4_14),
% 3.27/0.79    inference(avatar_split_clause,[],[f208,f214,f210])).
% 3.27/0.79  fof(f208,plain,(
% 3.27/0.79    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.27/0.79    inference(forward_demodulation,[],[f207,f156])).
% 3.27/0.79  fof(f156,plain,(
% 3.27/0.79    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 3.27/0.79    inference(resolution,[],[f77,f112])).
% 3.27/0.79  fof(f207,plain,(
% 3.27/0.79    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 3.27/0.79    inference(subsumption_resolution,[],[f192,f113])).
% 3.27/0.79  fof(f192,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 3.27/0.79    inference(resolution,[],[f79,f112])).
% 3.27/0.79  fof(f79,plain,(
% 3.27/0.79    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 3.27/0.79    inference(cnf_transformation,[],[f47])).
% 3.27/0.79  fof(f206,plain,(
% 3.27/0.79    spl4_11 | spl4_12),
% 3.27/0.79    inference(avatar_split_clause,[],[f197,f203,f199])).
% 3.27/0.79  fof(f197,plain,(
% 3.27/0.79    u1_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK1)),
% 3.27/0.79    inference(forward_demodulation,[],[f196,f155])).
% 3.27/0.79  fof(f155,plain,(
% 3.27/0.79    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 3.27/0.79    inference(resolution,[],[f77,f54])).
% 3.27/0.79  fof(f196,plain,(
% 3.27/0.79    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 3.27/0.79    inference(subsumption_resolution,[],[f191,f53])).
% 3.27/0.79  fof(f191,plain,(
% 3.27/0.79    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 3.27/0.79    inference(resolution,[],[f79,f54])).
% 3.27/0.79  fof(f111,plain,(
% 3.27/0.79    spl4_1 | spl4_2),
% 3.27/0.79    inference(avatar_split_clause,[],[f59,f107,f103])).
% 3.27/0.79  fof(f59,plain,(
% 3.27/0.79    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.27/0.79    inference(cnf_transformation,[],[f39])).
% 3.27/0.79  fof(f110,plain,(
% 3.27/0.79    ~spl4_1 | ~spl4_2),
% 3.27/0.79    inference(avatar_split_clause,[],[f60,f107,f103])).
% 3.27/0.79  fof(f60,plain,(
% 3.27/0.79    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.27/0.79    inference(cnf_transformation,[],[f39])).
% 3.27/0.79  % SZS output end Proof for theBenchmark
% 3.27/0.79  % (20134)------------------------------
% 3.27/0.79  % (20134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.79  % (20134)Termination reason: Refutation
% 3.27/0.79  
% 3.27/0.79  % (20134)Memory used [KB]: 13048
% 3.27/0.79  % (20134)Time elapsed: 0.378 s
% 3.27/0.79  % (20134)------------------------------
% 3.27/0.79  % (20134)------------------------------
% 3.27/0.80  % (20123)Success in time 0.438 s
%------------------------------------------------------------------------------
