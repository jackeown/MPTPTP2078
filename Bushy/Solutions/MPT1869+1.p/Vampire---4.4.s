%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t37_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:31 EDT 2019

% Result     : Theorem 8.29s
% Output     : Refutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :  179 (6568 expanded)
%              Number of leaves         :   30 (1342 expanded)
%              Depth                    :   21
%              Number of atoms          :  616 (46770 expanded)
%              Number of equality atoms :   52 (4325 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26803,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f995,f1570,f1687,f2433,f2482,f8715,f24433,f26789,f26801])).

fof(f26801,plain,
    ( ~ spl14_18
    | ~ spl14_22
    | ~ spl14_140 ),
    inference(avatar_contradiction_clause,[],[f26792])).

fof(f26792,plain,
    ( $false
    | ~ spl14_18
    | ~ spl14_22
    | ~ spl14_140 ),
    inference(unit_resulting_resolution,[],[f102,f26791])).

fof(f26791,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl14_18
    | ~ spl14_22
    | ~ spl14_140 ),
    inference(forward_demodulation,[],[f26790,f223])).

fof(f223,plain,(
    u1_struct_0(sK10(sK0,sK1)) = sK1 ),
    inference(unit_resulting_resolution,[],[f105,f103,f101,f201,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK10(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',t10_tsep_1)).

fof(f201,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f104,f103,f105,f102,f101,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',t35_tex_2)).

fof(f104,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',t37_tex_2)).

fof(f101,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f103,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f26790,plain,
    ( v2_tex_2(u1_struct_0(sK10(sK0,sK1)),sK0)
    | ~ spl14_18
    | ~ spl14_22
    | ~ spl14_140 ),
    inference(unit_resulting_resolution,[],[f103,f201,f105,f222,f101,f101,f24017,f5944])).

fof(f5944,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(u1_struct_0(sK10(sK0,X1)),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK10(sK0,X1),X0)
        | v2_struct_0(X0)
        | ~ v1_tdlat_3(sK10(sK0,X1))
        | ~ l1_pre_topc(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_18
    | ~ spl14_22 ),
    inference(duplicate_literal_removal,[],[f5940])).

fof(f5940,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK10(sK0,X1),X0)
        | v2_struct_0(X0)
        | ~ v1_tdlat_3(sK10(sK0,X1))
        | v2_tex_2(u1_struct_0(sK10(sK0,X1)),X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_18
    | ~ spl14_22 ),
    inference(resolution,[],[f1718,f1569])).

fof(f1569,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK10(sK0,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f1568])).

fof(f1568,plain,
    ( spl14_18
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v2_struct_0(sK10(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f1718,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK10(sK0,X4))
        | ~ l1_pre_topc(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_pre_topc(sK10(sK0,X4),X5)
        | v2_struct_0(X5)
        | ~ v1_tdlat_3(sK10(sK0,X4))
        | v2_tex_2(u1_struct_0(sK10(sK0,X4)),X5)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_22 ),
    inference(superposition,[],[f168,f1686])).

fof(f1686,plain,
    ( ! [X2] :
        ( u1_struct_0(sK10(sK0,X2)) = X2
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f1685])).

fof(f1685,plain,
    ( spl14_22
  <=> ! [X2] :
        ( v1_xboole_0(X2)
        | u1_struct_0(sK10(sK0,X2)) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',t26_tex_2)).

fof(f24017,plain,
    ( v1_tdlat_3(sK10(sK0,sK1))
    | ~ spl14_140 ),
    inference(avatar_component_clause,[],[f24016])).

fof(f24016,plain,
    ( spl14_140
  <=> v1_tdlat_3(sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_140])])).

fof(f222,plain,(
    m1_pre_topc(sK10(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f103,f105,f101,f201,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f102,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f26789,plain,
    ( ~ spl14_36
    | spl14_141
    | ~ spl14_150 ),
    inference(avatar_contradiction_clause,[],[f26783])).

fof(f26783,plain,
    ( $false
    | ~ spl14_36
    | ~ spl14_141
    | ~ spl14_150 ),
    inference(unit_resulting_resolution,[],[f293,f24594,f26761,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',t4_subset)).

fof(f26761,plain,
    ( ~ m1_subset_1(sK6(sK10(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl14_36
    | ~ spl14_141
    | ~ spl14_150 ),
    inference(forward_demodulation,[],[f26745,f223])).

fof(f26745,plain,
    ( ~ m1_subset_1(sK6(sK10(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK10(sK0,sK1))))
    | ~ spl14_36
    | ~ spl14_141
    | ~ spl14_150 ),
    inference(unit_resulting_resolution,[],[f276,f24034,f24594,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',d5_pre_topc)).

fof(f24034,plain,
    ( ~ v3_pre_topc(sK6(sK10(sK0,sK1)),sK10(sK0,sK1))
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f275,f276,f24020,f128])).

fof(f128,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK6(X0),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k1_tarski(X2) = X1
                 => v3_pre_topc(X1,X0) ) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',t19_tdlat_3)).

fof(f24020,plain,
    ( ~ v1_tdlat_3(sK10(sK0,sK1))
    | ~ spl14_141 ),
    inference(avatar_component_clause,[],[f24019])).

fof(f24019,plain,
    ( spl14_141
  <=> ~ v1_tdlat_3(sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_141])])).

fof(f275,plain,(
    v2_pre_topc(sK10(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f104,f105,f222,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',cc1_pre_topc)).

fof(f276,plain,(
    l1_pre_topc(sK10(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f105,f222,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',dt_m1_pre_topc)).

fof(f24594,plain,
    ( r2_hidden(sK6(sK10(sK0,sK1)),u1_pre_topc(sK10(sK0,sK1)))
    | ~ spl14_36
    | ~ spl14_141
    | ~ spl14_150 ),
    inference(forward_demodulation,[],[f24593,f24158])).

fof(f24158,plain,
    ( k3_xboole_0(sK1,sK2(sK7(sK10(sK0,sK1)))) = sK6(sK10(sK0,sK1))
    | ~ spl14_36
    | ~ spl14_141 ),
    inference(forward_demodulation,[],[f24147,f24156])).

fof(f24156,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK7(sK10(sK0,sK1))) = sK6(sK10(sK0,sK1))
    | ~ spl14_36
    | ~ spl14_141 ),
    inference(forward_demodulation,[],[f24151,f24033])).

fof(f24033,plain,
    ( k1_tarski(sK7(sK10(sK0,sK1))) = sK6(sK10(sK0,sK1))
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f275,f276,f24020,f127])).

fof(f127,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | k1_tarski(sK7(X0)) = sK6(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f24151,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK7(sK10(sK0,sK1))) = k1_tarski(sK7(sK10(sK0,sK1)))
    | ~ spl14_36
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f188,f24054,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',redefinition_k6_domain_1)).

fof(f24054,plain,
    ( m1_subset_1(sK7(sK10(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl14_36
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f24044,f2432])).

fof(f2432,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_36 ),
    inference(avatar_component_clause,[],[f2431])).

fof(f2431,plain,
    ( spl14_36
  <=> ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).

fof(f24044,plain,
    ( m1_subset_1(sK7(sK10(sK0,sK1)),sK1)
    | ~ spl14_141 ),
    inference(forward_demodulation,[],[f24032,f223])).

fof(f24032,plain,
    ( m1_subset_1(sK7(sK10(sK0,sK1)),u1_struct_0(sK10(sK0,sK1)))
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f275,f276,f24020,f126])).

fof(f126,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f188,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f103,f175,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',fc2_struct_0)).

fof(f175,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f105,f163])).

fof(f163,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',dt_l1_pre_topc)).

fof(f24147,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK7(sK10(sK0,sK1))) = k3_xboole_0(sK1,sK2(sK7(sK10(sK0,sK1))))
    | ~ spl14_36
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f24055,f24054,f215])).

fof(f215,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k6_domain_1(u1_struct_0(sK0),X2) = k3_xboole_0(sK1,sK2(X2))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(forward_demodulation,[],[f214,f148])).

fof(f148,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',commutativity_k3_xboole_0)).

fof(f214,plain,(
    ! [X2] :
      ( k6_domain_1(u1_struct_0(sK0),X2) = k3_xboole_0(sK2(X2),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(backward_demodulation,[],[f213,f100])).

fof(f100,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK2(X2)) = k6_domain_1(u1_struct_0(sK0),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f213,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),sK1,X0) = k3_xboole_0(X0,sK1) ),
    inference(forward_demodulation,[],[f202,f203])).

fof(f203,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f101,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',redefinition_k9_subset_1)).

fof(f202,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f101,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',commutativity_k9_subset_1)).

fof(f24055,plain,
    ( r2_hidden(sK7(sK10(sK0,sK1)),sK1)
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f201,f24044,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',t2_subset)).

fof(f24593,plain,
    ( r2_hidden(k3_xboole_0(sK1,sK2(sK7(sK10(sK0,sK1)))),u1_pre_topc(sK10(sK0,sK1)))
    | ~ spl14_36
    | ~ spl14_141
    | ~ spl14_150 ),
    inference(forward_demodulation,[],[f24578,f148])).

fof(f24578,plain,
    ( r2_hidden(k3_xboole_0(sK2(sK7(sK10(sK0,sK1))),sK1),u1_pre_topc(sK10(sK0,sK1)))
    | ~ spl14_36
    | ~ spl14_141
    | ~ spl14_150 ),
    inference(unit_resulting_resolution,[],[f24293,f24148,f331,f24432])).

fof(f24432,plain,
    ( ! [X2] :
        ( r2_hidden(k3_xboole_0(X2,sK1),u1_pre_topc(sK10(sK0,sK1)))
        | ~ r2_hidden(X2,u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(sK1)) )
    | ~ spl14_150 ),
    inference(avatar_component_clause,[],[f24431])).

fof(f24431,plain,
    ( spl14_150
  <=> ! [X2] :
        ( r2_hidden(k3_xboole_0(X2,sK1),u1_pre_topc(sK10(sK0,sK1)))
        | ~ r2_hidden(X2,u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_150])])).

fof(f331,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f320,f321])).

fof(f321,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,sK1),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f310,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',dt_k9_subset_1)).

fof(f310,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f309,f308])).

fof(f308,plain,(
    m1_subset_1(k2_struct_0(sK10(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f303,f223])).

fof(f303,plain,(
    m1_subset_1(k2_struct_0(sK10(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK10(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f282,f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',dt_k2_struct_0)).

fof(f282,plain,(
    l1_struct_0(sK10(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f276,f163])).

fof(f309,plain,(
    k2_struct_0(sK10(sK0,sK1)) = sK1 ),
    inference(forward_demodulation,[],[f302,f223])).

fof(f302,plain,(
    u1_struct_0(sK10(sK0,sK1)) = k2_struct_0(sK10(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f282,f159])).

fof(f159,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',d3_struct_0)).

fof(f320,plain,(
    ! [X0] : k9_subset_1(sK1,X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f310,f113])).

fof(f24148,plain,
    ( m1_subset_1(sK2(sK7(sK10(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_36
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f24055,f24054,f98])).

fof(f98,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_subset_1(sK2(X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f24293,plain,
    ( r2_hidden(sK2(sK7(sK10(sK0,sK1))),u1_pre_topc(sK0))
    | ~ spl14_36
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f105,f24149,f24148,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f24149,plain,
    ( v3_pre_topc(sK2(sK7(sK10(sK0,sK1))),sK0)
    | ~ spl14_36
    | ~ spl14_141 ),
    inference(unit_resulting_resolution,[],[f24055,f24054,f99])).

fof(f99,plain,(
    ! [X2] :
      ( v3_pre_topc(sK2(X2),sK0)
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f293,plain,(
    m1_subset_1(u1_pre_topc(sK10(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(forward_demodulation,[],[f281,f223])).

fof(f281,plain,(
    m1_subset_1(u1_pre_topc(sK10(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK10(sK0,sK1))))) ),
    inference(unit_resulting_resolution,[],[f276,f152])).

fof(f152,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',dt_u1_pre_topc)).

fof(f24433,plain,
    ( ~ spl14_63
    | spl14_150 ),
    inference(avatar_split_clause,[],[f1908,f24431,f8655])).

fof(f8655,plain,
    ( spl14_63
  <=> ~ l1_pre_topc(sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_63])])).

fof(f1908,plain,(
    ! [X2] :
      ( r2_hidden(k3_xboole_0(X2,sK1),u1_pre_topc(sK10(sK0,sK1)))
      | ~ m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK10(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1907,f320])).

fof(f1907,plain,(
    ! [X2] :
      ( r2_hidden(k9_subset_1(sK1,X2,sK1),u1_pre_topc(sK10(sK0,sK1)))
      | ~ m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK10(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1906,f223])).

fof(f1906,plain,(
    ! [X2] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK10(sK0,sK1)),X2,sK1),u1_pre_topc(sK10(sK0,sK1)))
      | ~ m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK10(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1905,f309])).

fof(f1905,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(sK10(sK0,sK1)),X2,k2_struct_0(sK10(sK0,sK1))),u1_pre_topc(sK10(sK0,sK1)))
      | ~ l1_pre_topc(sK10(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1904,f320])).

fof(f1904,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k9_subset_1(sK1,X2,sK1),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(sK10(sK0,sK1)),X2,k2_struct_0(sK10(sK0,sK1))),u1_pre_topc(sK10(sK0,sK1)))
      | ~ l1_pre_topc(sK10(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1903,f309])).

fof(f1903,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k9_subset_1(sK1,X2,k2_struct_0(sK10(sK0,sK1))),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(sK10(sK0,sK1)),X2,k2_struct_0(sK10(sK0,sK1))),u1_pre_topc(sK10(sK0,sK1)))
      | ~ l1_pre_topc(sK10(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1893,f223])).

fof(f1893,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK10(sK0,sK1)),X2,k2_struct_0(sK10(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK10(sK0,sK1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(sK10(sK0,sK1)),X2,k2_struct_0(sK10(sK0,sK1))),u1_pre_topc(sK10(sK0,sK1)))
      | ~ l1_pre_topc(sK10(sK0,sK1)) ) ),
    inference(resolution,[],[f185,f222])).

fof(f185,plain,(
    ! [X10,X11] :
      ( ~ m1_pre_topc(X10,sK0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X10),X11,k2_struct_0(X10)),k1_zfmisc_1(u1_struct_0(X10)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X11,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(X10),X11,k2_struct_0(X10)),u1_pre_topc(X10))
      | ~ l1_pre_topc(X10) ) ),
    inference(resolution,[],[f105,f169])).

fof(f169,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | r2_hidden(X2,u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t37_tex_2.p',d9_pre_topc)).

fof(f8715,plain,(
    spl14_63 ),
    inference(avatar_contradiction_clause,[],[f8698])).

fof(f8698,plain,
    ( $false
    | ~ spl14_63 ),
    inference(unit_resulting_resolution,[],[f222,f8656,f182])).

fof(f182,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK0)
      | l1_pre_topc(X9) ) ),
    inference(resolution,[],[f105,f147])).

fof(f8656,plain,
    ( ~ l1_pre_topc(sK10(sK0,sK1))
    | ~ spl14_63 ),
    inference(avatar_component_clause,[],[f8655])).

fof(f2482,plain,(
    ~ spl14_34 ),
    inference(avatar_contradiction_clause,[],[f2471])).

fof(f2471,plain,
    ( $false
    | ~ spl14_34 ),
    inference(unit_resulting_resolution,[],[f105,f104,f103,f102,f101,f2429,f108])).

fof(f2429,plain,
    ( v1_xboole_0(sK1)
    | ~ spl14_34 ),
    inference(avatar_component_clause,[],[f2428])).

fof(f2428,plain,
    ( spl14_34
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f2433,plain,
    ( spl14_34
    | spl14_36 ),
    inference(avatar_split_clause,[],[f450,f2431,f2428])).

fof(f450,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f207,f135])).

fof(f207,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f101,f133])).

fof(f1687,plain,
    ( spl14_22
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f172,f978,f1685])).

fof(f978,plain,
    ( spl14_5
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f172,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK10(sK0,X2)) = X2 ) ),
    inference(resolution,[],[f103,f144])).

fof(f1570,plain,
    ( spl14_18
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f170,f978,f1568])).

fof(f170,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_struct_0(sK10(sK0,X0)) ) ),
    inference(resolution,[],[f103,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK10(X0,X1)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f995,plain,(
    spl14_5 ),
    inference(avatar_contradiction_clause,[],[f984])).

fof(f984,plain,
    ( $false
    | ~ spl14_5 ),
    inference(unit_resulting_resolution,[],[f105,f979])).

fof(f979,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f978])).
%------------------------------------------------------------------------------
