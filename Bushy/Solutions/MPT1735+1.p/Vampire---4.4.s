%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t44_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:15 EDT 2019

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 421 expanded)
%              Number of leaves         :   44 ( 163 expanded)
%              Depth                    :   17
%              Number of atoms          :  973 (2280 expanded)
%              Number of equality atoms :   65 ( 101 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14998,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f194,f201,f208,f215,f222,f250,f257,f264,f271,f306,f325,f381,f400,f454,f851,f1038,f1524,f1582,f3110,f7509,f14512,f14981,f14993])).

fof(f14993,plain,
    ( ~ spl11_34
    | ~ spl11_48
    | spl11_57
    | ~ spl11_58
    | ~ spl11_608 ),
    inference(avatar_contradiction_clause,[],[f14992])).

fof(f14992,plain,
    ( $false
    | ~ spl11_34
    | ~ spl11_48
    | ~ spl11_57
    | ~ spl11_58
    | ~ spl11_608 ),
    inference(subsumption_resolution,[],[f14991,f399])).

fof(f399,plain,
    ( v2_pre_topc(sK1)
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl11_48
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f14991,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl11_34
    | ~ spl11_57
    | ~ spl11_58
    | ~ spl11_608 ),
    inference(subsumption_resolution,[],[f14990,f324])).

fof(f324,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl11_34
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f14990,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_57
    | ~ spl11_58
    | ~ spl11_608 ),
    inference(subsumption_resolution,[],[f14989,f450])).

fof(f450,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl11_58
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f14989,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_57
    | ~ spl11_608 ),
    inference(subsumption_resolution,[],[f14983,f447])).

fof(f447,plain,
    ( ~ v1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl11_57 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl11_57
  <=> ~ v1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f14983,plain,
    ( v1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_608 ),
    inference(resolution,[],[f14980,f509])).

fof(f509,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f181,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',t1_tsep_1)).

fof(f181,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',t16_tsep_1)).

fof(f14980,plain,
    ( v3_pre_topc(u1_struct_0(k2_tsep_1(sK0,sK2,sK1)),sK1)
    | ~ spl11_608 ),
    inference(avatar_component_clause,[],[f14979])).

fof(f14979,plain,
    ( spl11_608
  <=> v3_pre_topc(u1_struct_0(k2_tsep_1(sK0,sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_608])])).

fof(f14981,plain,
    ( spl11_608
    | ~ spl11_442
    | ~ spl11_594 ),
    inference(avatar_split_clause,[],[f14944,f14510,f7235,f14979])).

fof(f7235,plain,
    ( spl11_442
  <=> u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_442])])).

fof(f14510,plain,
    ( spl11_594
  <=> v3_pre_topc(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_594])])).

fof(f14944,plain,
    ( v3_pre_topc(u1_struct_0(k2_tsep_1(sK0,sK2,sK1)),sK1)
    | ~ spl11_442
    | ~ spl11_594 ),
    inference(backward_demodulation,[],[f7236,f14511])).

fof(f14511,plain,
    ( v3_pre_topc(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),sK1)
    | ~ spl11_594 ),
    inference(avatar_component_clause,[],[f14510])).

fof(f7236,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_442 ),
    inference(avatar_component_clause,[],[f7235])).

fof(f14512,plain,
    ( spl11_594
    | ~ spl11_16
    | ~ spl11_100
    | ~ spl11_324 ),
    inference(avatar_split_clause,[],[f14465,f3108,f849,f248,f14510])).

fof(f248,plain,
    ( spl11_16
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f849,plain,
    ( spl11_100
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f3108,plain,
    ( spl11_324
  <=> ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_324])])).

fof(f14465,plain,
    ( v3_pre_topc(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),sK1)
    | ~ spl11_16
    | ~ spl11_100
    | ~ spl11_324 ),
    inference(forward_demodulation,[],[f14464,f154])).

fof(f154,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',commutativity_k3_xboole_0)).

fof(f14464,plain,
    ( v3_pre_topc(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)),sK1)
    | ~ spl11_16
    | ~ spl11_100
    | ~ spl11_324 ),
    inference(forward_demodulation,[],[f14463,f768])).

fof(f768,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k9_subset_1(X1,X0,X1) ),
    inference(resolution,[],[f456,f282])).

fof(f282,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f153,f152])).

fof(f152,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',idempotence_k3_xboole_0)).

fof(f153,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',t17_xboole_1)).

fof(f456,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | k3_xboole_0(X0,X1) = k9_subset_1(X2,X0,X1) ) ),
    inference(resolution,[],[f169,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',t3_subset)).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',redefinition_k9_subset_1)).

fof(f14463,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK1)),sK1)
    | ~ spl11_16
    | ~ spl11_100
    | ~ spl11_324 ),
    inference(forward_demodulation,[],[f14462,f850])).

fof(f850,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl11_100 ),
    inference(avatar_component_clause,[],[f849])).

fof(f14462,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),sK1)
    | ~ spl11_16
    | ~ spl11_100
    | ~ spl11_324 ),
    inference(subsumption_resolution,[],[f14461,f5759])).

fof(f5759,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) ),
    inference(subsumption_resolution,[],[f5750,f282])).

fof(f5750,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1))
      | ~ r1_tarski(X1,X1) ) ),
    inference(resolution,[],[f1310,f164])).

fof(f1310,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X3))
      | m1_subset_1(k3_xboole_0(X4,X3),k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f168,f768])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',dt_k9_subset_1)).

fof(f14461,plain,
    ( ~ m1_subset_1(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),sK1)
    | ~ spl11_16
    | ~ spl11_100
    | ~ spl11_324 ),
    inference(forward_demodulation,[],[f14460,f768])).

fof(f14460,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),sK1)
    | ~ spl11_16
    | ~ spl11_100
    | ~ spl11_324 ),
    inference(forward_demodulation,[],[f14453,f850])).

fof(f14453,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),sK1)
    | ~ spl11_16
    | ~ spl11_324 ),
    inference(resolution,[],[f3109,f249])).

fof(f249,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f248])).

fof(f3109,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),X0) )
    | ~ spl11_324 ),
    inference(avatar_component_clause,[],[f3108])).

fof(f7509,plain,
    ( spl11_442
    | ~ spl11_180 ),
    inference(avatar_split_clause,[],[f1562,f1522,f7235])).

fof(f1522,plain,
    ( spl11_180
  <=> u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_180])])).

fof(f1562,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_180 ),
    inference(superposition,[],[f154,f1523])).

fof(f1523,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_180 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f3110,plain,
    ( spl11_324
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_18
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f1125,f262,f255,f206,f199,f3108])).

fof(f199,plain,
    ( spl11_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f206,plain,
    ( spl11_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f255,plain,
    ( spl11_18
  <=> v1_tsep_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f262,plain,
    ( spl11_20
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1125,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),X0) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_18
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f1124,f200])).

fof(f200,plain,
    ( v2_pre_topc(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_4
    | ~ spl11_18
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f1123,f263])).

fof(f263,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f1120,f207])).

fof(f207,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f206])).

fof(f1120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_struct_0(X0)),X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_18 ),
    inference(resolution,[],[f586,f256])).

fof(f256,plain,
    ( v1_tsep_1(sK2,sK0)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f255])).

fof(f586,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_tsep_1(X5,X6)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X4),u1_struct_0(X5),k2_struct_0(X4)),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_pre_topc(X4,X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X5,X6)
      | v3_pre_topc(k9_subset_1(u1_struct_0(X4),u1_struct_0(X5),k2_struct_0(X4)),X4)
      | ~ v2_pre_topc(X6) ) ),
    inference(subsumption_resolution,[],[f583,f132])).

fof(f583,plain,(
    ! [X6,X4,X5] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X4),u1_struct_0(X5),k2_struct_0(X4)),X4)
      | ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(u1_struct_0(X6)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X4),u1_struct_0(X5),k2_struct_0(X4)),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_pre_topc(X4,X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X5,X6)
      | ~ v1_tsep_1(X5,X6)
      | ~ v2_pre_topc(X6) ) ),
    inference(duplicate_literal_removal,[],[f582])).

fof(f582,plain,(
    ! [X6,X4,X5] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X4),u1_struct_0(X5),k2_struct_0(X4)),X4)
      | ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(u1_struct_0(X6)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X4),u1_struct_0(X5),k2_struct_0(X4)),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_pre_topc(X4,X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X5,X6)
      | ~ v1_tsep_1(X5,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6) ) ),
    inference(resolution,[],[f178,f518])).

fof(f518,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f187,f132])).

fof(f187,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f178,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_pre_topc(X3,X0)
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK3(X0,X1,X2),X0)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f96,f97])).

fof(f97,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',t32_tops_2)).

fof(f1582,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | spl11_7
    | spl11_9
    | ~ spl11_16
    | ~ spl11_20
    | spl11_23
    | spl11_59 ),
    inference(avatar_contradiction_clause,[],[f1581])).

fof(f1581,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_23
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f1580,f193])).

fof(f193,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1580,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_23
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f1579,f200])).

fof(f1579,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_23
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f1578,f207])).

fof(f1578,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_23
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f1577,f221])).

fof(f221,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl11_9
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f1577,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_23
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f1576,f263])).

fof(f1576,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_23
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f1575,f214])).

fof(f214,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl11_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1575,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_16
    | ~ spl11_23
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f1574,f249])).

fof(f1574,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_23
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f1572,f270])).

fof(f270,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl11_23
  <=> ~ r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f1572,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_59 ),
    inference(resolution,[],[f453,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',t30_tsep_1)).

fof(f453,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl11_59 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl11_59
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f1524,plain,
    ( spl11_180
    | spl11_7
    | ~ spl11_16
    | spl11_23
    | ~ spl11_116 ),
    inference(avatar_split_clause,[],[f1051,f1036,f269,f248,f213,f1522])).

fof(f1036,plain,
    ( spl11_116
  <=> ! [X17] :
        ( r1_tsep_1(sK2,X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(X17)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X17)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X17)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_116])])).

fof(f1051,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_23
    | ~ spl11_116 ),
    inference(subsumption_resolution,[],[f1050,f214])).

fof(f1050,plain,
    ( v2_struct_0(sK1)
    | u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_16
    | ~ spl11_23
    | ~ spl11_116 ),
    inference(subsumption_resolution,[],[f1048,f249])).

fof(f1048,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_23
    | ~ spl11_116 ),
    inference(resolution,[],[f1037,f270])).

fof(f1037,plain,
    ( ! [X17] :
        ( r1_tsep_1(sK2,X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(X17)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X17)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X17)) )
    | ~ spl11_116 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f1038,plain,
    ( spl11_116
    | spl11_1
    | ~ spl11_4
    | spl11_9
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f632,f262,f220,f206,f192,f1036])).

fof(f632,plain,
    ( ! [X17] :
        ( r1_tsep_1(sK2,X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(X17)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X17)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X17)) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f631,f193])).

fof(f631,plain,
    ( ! [X17] :
        ( r1_tsep_1(sK2,X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(X17)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X17)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X17))
        | v2_struct_0(sK0) )
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f630,f207])).

fof(f630,plain,
    ( ! [X17] :
        ( r1_tsep_1(sK2,X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(X17)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X17)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X17))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f615,f221])).

fof(f615,plain,
    ( ! [X17] :
        ( r1_tsep_1(sK2,X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(X17)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X17)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X17))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20 ),
    inference(resolution,[],[f607,f263])).

fof(f607,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f606,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',dt_k2_tsep_1)).

fof(f606,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f605,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f605,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f179,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',d5_tsep_1)).

fof(f851,plain,
    ( spl11_100
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f672,f323,f849])).

fof(f672,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl11_34 ),
    inference(resolution,[],[f300,f324])).

fof(f300,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f125,f128])).

fof(f128,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',dt_l1_pre_topc)).

fof(f125,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',d3_struct_0)).

fof(f454,plain,
    ( ~ spl11_57
    | ~ spl11_59 ),
    inference(avatar_split_clause,[],[f122,f452,f446])).

fof(f122,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ v1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,
    ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
      | ~ v1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1) )
    & ~ r1_tsep_1(sK2,sK1)
    & m1_pre_topc(sK2,sK0)
    & v1_tsep_1(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f93,f92,f91])).

fof(f91,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  | ~ v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
                & ~ r1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X2,X1),X1)
                | ~ v1_tsep_1(k2_tsep_1(sK0,X2,X1),X1) )
              & ~ r1_tsep_1(X2,X1)
              & m1_pre_topc(X2,sK0)
              & v1_tsep_1(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                | ~ v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              & ~ r1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,sK1),sK1)
              | ~ v1_tsep_1(k2_tsep_1(X0,X2,sK1),sK1) )
            & ~ r1_tsep_1(X2,sK1)
            & m1_pre_topc(X2,X0)
            & v1_tsep_1(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
            | ~ v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
          & ~ r1_tsep_1(X2,X1)
          & m1_pre_topc(X2,X0)
          & v1_tsep_1(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_pre_topc(k2_tsep_1(X0,sK2,X1),X1)
          | ~ v1_tsep_1(k2_tsep_1(X0,sK2,X1),X1) )
        & ~ r1_tsep_1(sK2,X1)
        & m1_pre_topc(sK2,X0)
        & v1_tsep_1(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                | ~ v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              & ~ r1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                | ~ v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              & ~ r1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X2,X1)
                 => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                    & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',t44_tmap_1)).

fof(f400,plain,
    ( spl11_48
    | ~ spl11_16
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f386,f379,f248,f398])).

fof(f379,plain,
    ( spl11_46
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f386,plain,
    ( v2_pre_topc(sK1)
    | ~ spl11_16
    | ~ spl11_46 ),
    inference(resolution,[],[f380,f249])).

fof(f380,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) )
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f379])).

fof(f381,plain,
    ( spl11_46
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f377,f206,f199,f379])).

fof(f377,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) )
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f375,f207])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_pre_topc(X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f147,f200])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',cc1_pre_topc)).

fof(f325,plain,
    ( spl11_34
    | ~ spl11_16
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f313,f304,f248,f323])).

fof(f304,plain,
    ( spl11_32
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f313,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_16
    | ~ spl11_32 ),
    inference(resolution,[],[f305,f249])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f304])).

fof(f306,plain,
    ( spl11_32
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f301,f206,f304])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl11_4 ),
    inference(resolution,[],[f131,f207])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t44_tmap_1.p',dt_m1_pre_topc)).

fof(f271,plain,(
    ~ spl11_23 ),
    inference(avatar_split_clause,[],[f121,f269])).

fof(f121,plain,(
    ~ r1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f94])).

fof(f264,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f120,f262])).

fof(f120,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f94])).

fof(f257,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f119,f255])).

fof(f119,plain,(
    v1_tsep_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f94])).

fof(f250,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f117,f248])).

fof(f117,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f94])).

fof(f222,plain,(
    ~ spl11_9 ),
    inference(avatar_split_clause,[],[f118,f220])).

fof(f118,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f94])).

fof(f215,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f116,f213])).

fof(f116,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f94])).

fof(f208,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f115,f206])).

fof(f115,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f94])).

fof(f201,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f114,f199])).

fof(f114,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f94])).

fof(f194,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f113,f192])).

fof(f113,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f94])).
%------------------------------------------------------------------------------
