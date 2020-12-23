%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:06 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 932 expanded)
%              Number of leaves         :   34 ( 382 expanded)
%              Depth                    :   19
%              Number of atoms          :  769 (5358 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1714,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f271,f280,f301,f656,f1435,f1467,f1485,f1507,f1520,f1586,f1664,f1713])).

fof(f1713,plain,(
    spl11_23 ),
    inference(avatar_contradiction_clause,[],[f1712])).

fof(f1712,plain,
    ( $false
    | spl11_23 ),
    inference(subsumption_resolution,[],[f1711,f72])).

fof(f72,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK6,sK7),u1_struct_0(k9_yellow_6(sK4,sK5)))
    & m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK4,sK5)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK4,sK5)))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f19,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK4,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK4,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK4,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK4,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK4,sK5)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,sK5))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK4,sK5))) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK4,sK5)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,sK5))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK4,sK5))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(sK6,X3),u1_struct_0(k9_yellow_6(sK4,sK5)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,sK5))) )
      & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k3_xboole_0(sK6,X3),u1_struct_0(k9_yellow_6(sK4,sK5)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,sK5))) )
   => ( ~ m1_subset_1(k3_xboole_0(sK6,sK7),u1_struct_0(k9_yellow_6(sK4,sK5)))
      & m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

fof(f1711,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl11_23 ),
    inference(resolution,[],[f1686,f454])).

fof(f454,plain,(
    m1_connsp_2(sK7,sK4,sK5) ),
    inference(subsumption_resolution,[],[f453,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f453,plain,
    ( m1_connsp_2(sK7,sK4,sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f452,f70])).

fof(f70,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f452,plain,
    ( m1_connsp_2(sK7,sK4,sK5)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f451,f71])).

fof(f71,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f451,plain,
    ( m1_connsp_2(sK7,sK4,sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f444,f72])).

fof(f444,plain,
    ( m1_connsp_2(sK7,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f82,f74])).

fof(f74,plain,(
    m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f1686,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl11_23 ),
    inference(subsumption_resolution,[],[f1685,f69])).

fof(f1685,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | v2_struct_0(sK4) )
    | spl11_23 ),
    inference(subsumption_resolution,[],[f1684,f70])).

fof(f1684,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl11_23 ),
    inference(subsumption_resolution,[],[f1680,f71])).

fof(f1680,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl11_23 ),
    inference(resolution,[],[f1585,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f1585,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_23 ),
    inference(avatar_component_clause,[],[f1583])).

fof(f1583,plain,
    ( spl11_23
  <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f1664,plain,(
    spl11_22 ),
    inference(avatar_contradiction_clause,[],[f1663])).

fof(f1663,plain,
    ( $false
    | spl11_22 ),
    inference(subsumption_resolution,[],[f1662,f72])).

fof(f1662,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl11_22 ),
    inference(resolution,[],[f1595,f450])).

fof(f450,plain,(
    m1_connsp_2(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f449,f69])).

fof(f449,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f448,f70])).

fof(f448,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f447,f71])).

fof(f447,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f443,f72])).

fof(f443,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f82,f73])).

fof(f73,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    inference(cnf_transformation,[],[f46])).

fof(f1595,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl11_22 ),
    inference(subsumption_resolution,[],[f1594,f69])).

fof(f1594,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | v2_struct_0(sK4) )
    | spl11_22 ),
    inference(subsumption_resolution,[],[f1593,f70])).

fof(f1593,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl11_22 ),
    inference(subsumption_resolution,[],[f1589,f71])).

fof(f1589,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl11_22 ),
    inference(resolution,[],[f1581,f93])).

fof(f1581,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_22 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f1579,plain,
    ( spl11_22
  <=> m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f1586,plain,
    ( ~ spl11_22
    | ~ spl11_23
    | ~ spl11_8
    | ~ spl11_10
    | spl11_21 ),
    inference(avatar_split_clause,[],[f1577,f1504,f277,f268,f1583,f1579])).

fof(f268,plain,
    ( spl11_8
  <=> sP0(sK4,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f277,plain,
    ( spl11_10
  <=> sP0(sK4,sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f1504,plain,
    ( spl11_21
  <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK6,sK7)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f1577,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl11_8
    | ~ spl11_10
    | spl11_21 ),
    inference(subsumption_resolution,[],[f1576,f70])).

fof(f1576,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ spl11_8
    | ~ spl11_10
    | spl11_21 ),
    inference(subsumption_resolution,[],[f1575,f71])).

fof(f1575,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ spl11_8
    | ~ spl11_10
    | spl11_21 ),
    inference(subsumption_resolution,[],[f1574,f1436])).

fof(f1436,plain,
    ( v3_pre_topc(sK6,sK4)
    | ~ spl11_8 ),
    inference(resolution,[],[f270,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v3_pre_topc(X1,X0)
        | ~ r2_hidden(X2,X1) )
      & ( ( v3_pre_topc(X1,X0)
          & r2_hidden(X2,X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ( v3_pre_topc(X2,X0)
        & r2_hidden(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f270,plain,
    ( sP0(sK4,sK6,sK5)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f268])).

fof(f1574,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ spl11_10
    | spl11_21 ),
    inference(subsumption_resolution,[],[f1567,f1468])).

fof(f1468,plain,
    ( v3_pre_topc(sK7,sK4)
    | ~ spl11_10 ),
    inference(resolution,[],[f279,f79])).

fof(f279,plain,
    ( sP0(sK4,sK7,sK5)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f277])).

fof(f1567,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK7,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | spl11_21 ),
    inference(resolution,[],[f1506,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f99,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f1506,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK6,sK7)),sK4)
    | spl11_21 ),
    inference(avatar_component_clause,[],[f1504])).

fof(f1520,plain,
    ( ~ spl11_8
    | ~ spl11_10
    | spl11_20 ),
    inference(avatar_contradiction_clause,[],[f1519])).

fof(f1519,plain,
    ( $false
    | ~ spl11_8
    | ~ spl11_10
    | spl11_20 ),
    inference(subsumption_resolution,[],[f1518,f1437])).

fof(f1437,plain,
    ( r2_hidden(sK5,sK6)
    | ~ spl11_8 ),
    inference(resolution,[],[f270,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1518,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ spl11_10
    | spl11_20 ),
    inference(subsumption_resolution,[],[f1517,f1469])).

fof(f1469,plain,
    ( r2_hidden(sK5,sK7)
    | ~ spl11_10 ),
    inference(resolution,[],[f279,f78])).

fof(f1517,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ r2_hidden(sK5,sK6)
    | spl11_20 ),
    inference(resolution,[],[f1508,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1508,plain,
    ( ~ sP2(sK7,sK5,sK6)
    | spl11_20 ),
    inference(resolution,[],[f1502,f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X0)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(resolution,[],[f102,f116])).

fof(f116,plain,(
    ! [X0,X1] : sP3(X0,X1,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f108,f86])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f40,f39])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f64])).

% (12718)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% (12716)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% (12717)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK10(X0,X1,X2),X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP2(X1,sK10(X0,X1,X2),X0)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK10(X0,X1,X2),X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP2(X1,sK10(X0,X1,X2),X0)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f1502,plain,
    ( ~ r2_hidden(sK5,k1_setfam_1(k2_tarski(sK6,sK7)))
    | spl11_20 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f1500,plain,
    ( spl11_20
  <=> r2_hidden(sK5,k1_setfam_1(k2_tarski(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1507,plain,
    ( ~ spl11_20
    | ~ spl11_21
    | spl11_12 ),
    inference(avatar_split_clause,[],[f1492,f298,f1504,f1500])).

fof(f298,plain,
    ( spl11_12
  <=> sP0(sK4,k1_setfam_1(k2_tarski(sK6,sK7)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1492,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK6,sK7)),sK4)
    | ~ r2_hidden(sK5,k1_setfam_1(k2_tarski(sK6,sK7)))
    | spl11_12 ),
    inference(resolution,[],[f300,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f300,plain,
    ( ~ sP0(sK4,k1_setfam_1(k2_tarski(sK6,sK7)),sK5)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f298])).

fof(f1485,plain,(
    spl11_11 ),
    inference(avatar_contradiction_clause,[],[f1484])).

fof(f1484,plain,
    ( $false
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1483,f72])).

fof(f1483,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl11_11 ),
    inference(resolution,[],[f1463,f454])).

fof(f1463,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1462,f69])).

fof(f1462,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | v2_struct_0(sK4) )
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1461,f70])).

fof(f1461,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1457,f71])).

fof(f1457,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl11_11 ),
    inference(resolution,[],[f1455,f93])).

fof(f1455,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1454,f69])).

fof(f1454,plain,
    ( v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1453,f70])).

fof(f1453,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1452,f71])).

fof(f1452,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1451,f72])).

fof(f1451,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_11 ),
    inference(duplicate_literal_removal,[],[f1438])).

fof(f1438,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_11 ),
    inference(resolution,[],[f355,f303])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ sP1(sK5,k9_subset_1(X0,sK6,sK7),sK4)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(X0)) )
    | spl11_11 ),
    inference(superposition,[],[f296,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f98,f86])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f296,plain,
    ( ~ sP1(sK5,k1_setfam_1(k2_tarski(sK6,sK7)),sK4)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl11_11
  <=> sP1(sK5,k1_setfam_1(k2_tarski(sK6,sK7)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f355,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,k9_subset_1(u1_struct_0(X1),X2,X3),X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f81,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f37,f36])).

fof(f37,plain,(
    ! [X1,X2,X0] :
      ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f1467,plain,(
    spl11_9 ),
    inference(avatar_contradiction_clause,[],[f1466])).

fof(f1466,plain,
    ( $false
    | spl11_9 ),
    inference(subsumption_resolution,[],[f1465,f72])).

fof(f1465,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl11_9 ),
    inference(resolution,[],[f1431,f454])).

fof(f1431,plain,
    ( ! [X4] :
        ( ~ m1_connsp_2(sK7,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f1430,f72])).

fof(f1430,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_connsp_2(sK7,sK4,X4)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f1429,f69])).

fof(f1429,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK4))
        | v2_struct_0(sK4)
        | ~ m1_connsp_2(sK7,sK4,X4)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f1428,f70])).

fof(f1428,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ m1_connsp_2(sK7,sK4,X4)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f1414,f71])).

fof(f1414,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ m1_connsp_2(sK7,sK4,X4)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_9 ),
    inference(resolution,[],[f408,f275])).

fof(f275,plain,
    ( ~ sP1(sK5,sK7,sK4)
    | spl11_9 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl11_9
  <=> sP1(sK5,sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f408,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(X3,X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f93,f81])).

fof(f1435,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f1434])).

fof(f1434,plain,
    ( $false
    | spl11_7 ),
    inference(subsumption_resolution,[],[f1433,f72])).

fof(f1433,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl11_7 ),
    inference(resolution,[],[f1427,f450])).

fof(f1427,plain,
    ( ! [X3] :
        ( ~ m1_connsp_2(sK6,sK4,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
    | spl11_7 ),
    inference(subsumption_resolution,[],[f1426,f72])).

fof(f1426,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_connsp_2(sK6,sK4,X3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_7 ),
    inference(subsumption_resolution,[],[f1425,f69])).

fof(f1425,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK4))
        | v2_struct_0(sK4)
        | ~ m1_connsp_2(sK6,sK4,X3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_7 ),
    inference(subsumption_resolution,[],[f1424,f70])).

fof(f1424,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ m1_connsp_2(sK6,sK4,X3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_7 ),
    inference(subsumption_resolution,[],[f1413,f71])).

fof(f1413,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ m1_connsp_2(sK6,sK4,X3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_7 ),
    inference(resolution,[],[f408,f266])).

fof(f266,plain,
    ( ~ sP1(sK5,sK6,sK4)
    | spl11_7 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl11_7
  <=> sP1(sK5,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f656,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f637,f142])).

fof(f142,plain,
    ( spl11_5
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f637,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(resolution,[],[f629,f187])).

fof(f187,plain,(
    ~ sP3(sK6,sK7,sK7) ),
    inference(resolution,[],[f180,f74])).

fof(f180,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK4,sK5)))
      | ~ sP3(sK6,sK7,X1) ) ),
    inference(superposition,[],[f110,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f109,f86])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f110,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK6,sK7)),u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    inference(definition_unfolding,[],[f75,f86])).

fof(f75,plain,(
    ~ m1_subset_1(k3_xboole_0(sK6,sK7),u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    inference(cnf_transformation,[],[f46])).

fof(f629,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f628,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f628,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1,X1),X1)
      | sP3(X0,X1,X1) ) ),
    inference(factoring,[],[f310])).

fof(f310,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK10(X3,X4,X5),X5)
      | sP3(X3,X4,X5)
      | r2_hidden(sK10(X3,X4,X5),X4) ) ),
    inference(resolution,[],[f103,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,sK10(X0,X1,X2),X0)
      | sP3(X0,X1,X2)
      | r2_hidden(sK10(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f301,plain,
    ( ~ spl11_11
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f290,f298,f294])).

fof(f290,plain,
    ( ~ sP0(sK4,k1_setfam_1(k2_tarski(sK6,sK7)),sK5)
    | ~ sP1(sK5,k1_setfam_1(k2_tarski(sK6,sK7)),sK4) ),
    inference(resolution,[],[f77,f118])).

fof(f118,plain,(
    ~ r2_hidden(k1_setfam_1(k2_tarski(sK6,sK7)),u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    inference(resolution,[],[f92,f110])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f280,plain,
    ( ~ spl11_9
    | spl11_10
    | spl11_3 ),
    inference(avatar_split_clause,[],[f260,f133,f277,f273])).

fof(f133,plain,
    ( spl11_3
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f260,plain,
    ( sP0(sK4,sK7,sK5)
    | ~ sP1(sK5,sK7,sK4)
    | spl11_3 ),
    inference(resolution,[],[f76,f161])).

fof(f161,plain,
    ( r2_hidden(sK7,u1_struct_0(k9_yellow_6(sK4,sK5)))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f156,f135])).

fof(f135,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5)))
    | spl11_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f156,plain,
    ( r2_hidden(sK7,u1_struct_0(k9_yellow_6(sK4,sK5)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    inference(resolution,[],[f87,f74])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f271,plain,
    ( ~ spl11_7
    | spl11_8
    | spl11_3 ),
    inference(avatar_split_clause,[],[f259,f133,f268,f264])).

fof(f259,plain,
    ( sP0(sK4,sK6,sK5)
    | ~ sP1(sK5,sK6,sK4)
    | spl11_3 ),
    inference(resolution,[],[f76,f160])).

fof(f160,plain,
    ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK4,sK5)))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f155,f135])).

fof(f155,plain,
    ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK4,sK5)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    inference(resolution,[],[f87,f73])).

fof(f145,plain,
    ( ~ spl11_3
    | spl11_5 ),
    inference(avatar_split_clause,[],[f121,f142,f133])).

fof(f121,plain,
    ( v1_xboole_0(sK7)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5))) ),
    inference(resolution,[],[f89,f74])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:44:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (12694)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (12694)Refutation not found, incomplete strategy% (12694)------------------------------
% 0.20/0.50  % (12694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12702)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (12694)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12694)Memory used [KB]: 10618
% 0.20/0.51  % (12694)Time elapsed: 0.094 s
% 0.20/0.51  % (12694)------------------------------
% 0.20/0.51  % (12694)------------------------------
% 0.20/0.51  % (12699)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (12710)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (12696)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (12690)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (12695)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (12695)Refutation not found, incomplete strategy% (12695)------------------------------
% 0.20/0.52  % (12695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12695)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12695)Memory used [KB]: 10618
% 0.20/0.52  % (12695)Time elapsed: 0.113 s
% 0.20/0.52  % (12695)------------------------------
% 0.20/0.52  % (12695)------------------------------
% 0.20/0.52  % (12686)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (12707)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (12714)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (12685)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (12706)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (12704)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (12684)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (12701)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (12684)Refutation not found, incomplete strategy% (12684)------------------------------
% 0.20/0.53  % (12684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12684)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12684)Memory used [KB]: 1663
% 0.20/0.53  % (12684)Time elapsed: 0.120 s
% 0.20/0.53  % (12684)------------------------------
% 0.20/0.53  % (12684)------------------------------
% 0.20/0.53  % (12688)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (12698)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (12689)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (12687)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (12691)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (12693)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (12705)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (12693)Refutation not found, incomplete strategy% (12693)------------------------------
% 0.20/0.54  % (12693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12693)Memory used [KB]: 10618
% 0.20/0.54  % (12693)Time elapsed: 0.137 s
% 0.20/0.54  % (12693)------------------------------
% 0.20/0.54  % (12693)------------------------------
% 0.20/0.54  % (12708)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (12713)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (12692)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (12697)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (12703)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (12701)Refutation not found, incomplete strategy% (12701)------------------------------
% 0.20/0.55  % (12701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12701)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12701)Memory used [KB]: 10618
% 0.20/0.55  % (12701)Time elapsed: 0.148 s
% 0.20/0.55  % (12701)------------------------------
% 0.20/0.55  % (12701)------------------------------
% 0.20/0.55  % (12709)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (12700)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (12706)Refutation not found, incomplete strategy% (12706)------------------------------
% 0.20/0.55  % (12706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12706)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12706)Memory used [KB]: 10874
% 0.20/0.55  % (12706)Time elapsed: 0.147 s
% 0.20/0.55  % (12706)------------------------------
% 0.20/0.55  % (12706)------------------------------
% 0.20/0.56  % (12712)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.10/0.64  % (12715)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.67  % (12712)Refutation found. Thanks to Tanya!
% 2.10/0.67  % SZS status Theorem for theBenchmark
% 2.10/0.67  % SZS output start Proof for theBenchmark
% 2.10/0.67  fof(f1714,plain,(
% 2.10/0.67    $false),
% 2.10/0.67    inference(avatar_sat_refutation,[],[f145,f271,f280,f301,f656,f1435,f1467,f1485,f1507,f1520,f1586,f1664,f1713])).
% 2.10/0.67  fof(f1713,plain,(
% 2.10/0.67    spl11_23),
% 2.10/0.67    inference(avatar_contradiction_clause,[],[f1712])).
% 2.10/0.67  fof(f1712,plain,(
% 2.10/0.67    $false | spl11_23),
% 2.10/0.67    inference(subsumption_resolution,[],[f1711,f72])).
% 2.10/0.67  fof(f72,plain,(
% 2.10/0.67    m1_subset_1(sK5,u1_struct_0(sK4))),
% 2.10/0.67    inference(cnf_transformation,[],[f46])).
% 2.10/0.67  fof(f46,plain,(
% 2.10/0.67    (((~m1_subset_1(k3_xboole_0(sK6,sK7),u1_struct_0(k9_yellow_6(sK4,sK5))) & m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK4,sK5)))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK4,sK5)))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 2.10/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f19,f45,f44,f43,f42])).
% 2.10/0.67  fof(f42,plain,(
% 2.10/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK4,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK4,X1)))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f43,plain,(
% 2.10/0.67    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK4,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK4,X1)))) & m1_subset_1(X1,u1_struct_0(sK4))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK4,sK5))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,sK5)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK4,sK5)))) & m1_subset_1(sK5,u1_struct_0(sK4)))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f44,plain,(
% 2.10/0.67    ? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK4,sK5))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,sK5)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK4,sK5)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK6,X3),u1_struct_0(k9_yellow_6(sK4,sK5))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,sK5)))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK4,sK5))))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f45,plain,(
% 2.10/0.67    ? [X3] : (~m1_subset_1(k3_xboole_0(sK6,X3),u1_struct_0(k9_yellow_6(sK4,sK5))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK4,sK5)))) => (~m1_subset_1(k3_xboole_0(sK6,sK7),u1_struct_0(k9_yellow_6(sK4,sK5))) & m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK4,sK5))))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f19,plain,(
% 2.10/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.10/0.67    inference(flattening,[],[f18])).
% 2.10/0.67  fof(f18,plain,(
% 2.10/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f17])).
% 2.10/0.67  fof(f17,negated_conjecture,(
% 2.10/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.10/0.67    inference(negated_conjecture,[],[f16])).
% 2.10/0.67  fof(f16,conjecture,(
% 2.10/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).
% 2.10/0.67  fof(f1711,plain,(
% 2.10/0.67    ~m1_subset_1(sK5,u1_struct_0(sK4)) | spl11_23),
% 2.10/0.67    inference(resolution,[],[f1686,f454])).
% 2.10/0.67  fof(f454,plain,(
% 2.10/0.67    m1_connsp_2(sK7,sK4,sK5)),
% 2.10/0.67    inference(subsumption_resolution,[],[f453,f69])).
% 2.10/0.67  fof(f69,plain,(
% 2.10/0.67    ~v2_struct_0(sK4)),
% 2.10/0.67    inference(cnf_transformation,[],[f46])).
% 2.10/0.67  fof(f453,plain,(
% 2.10/0.67    m1_connsp_2(sK7,sK4,sK5) | v2_struct_0(sK4)),
% 2.10/0.67    inference(subsumption_resolution,[],[f452,f70])).
% 2.10/0.67  fof(f70,plain,(
% 2.10/0.67    v2_pre_topc(sK4)),
% 2.10/0.67    inference(cnf_transformation,[],[f46])).
% 2.10/0.67  fof(f452,plain,(
% 2.10/0.67    m1_connsp_2(sK7,sK4,sK5) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 2.10/0.67    inference(subsumption_resolution,[],[f451,f71])).
% 2.10/0.67  fof(f71,plain,(
% 2.10/0.67    l1_pre_topc(sK4)),
% 2.10/0.67    inference(cnf_transformation,[],[f46])).
% 2.10/0.67  fof(f451,plain,(
% 2.10/0.67    m1_connsp_2(sK7,sK4,sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 2.10/0.67    inference(subsumption_resolution,[],[f444,f72])).
% 2.10/0.67  fof(f444,plain,(
% 2.10/0.67    m1_connsp_2(sK7,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 2.10/0.67    inference(resolution,[],[f82,f74])).
% 2.10/0.67  fof(f74,plain,(
% 2.10/0.67    m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.67    inference(cnf_transformation,[],[f46])).
% 2.10/0.67  fof(f82,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f23])).
% 2.10/0.67  fof(f23,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.67    inference(flattening,[],[f22])).
% 2.10/0.67  fof(f22,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f15])).
% 2.10/0.67  fof(f15,axiom,(
% 2.10/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 2.10/0.67  fof(f1686,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_connsp_2(sK7,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4))) ) | spl11_23),
% 2.10/0.67    inference(subsumption_resolution,[],[f1685,f69])).
% 2.10/0.67  fof(f1685,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_connsp_2(sK7,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | v2_struct_0(sK4)) ) | spl11_23),
% 2.10/0.67    inference(subsumption_resolution,[],[f1684,f70])).
% 2.10/0.67  fof(f1684,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_connsp_2(sK7,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | spl11_23),
% 2.10/0.67    inference(subsumption_resolution,[],[f1680,f71])).
% 2.10/0.67  fof(f1680,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_connsp_2(sK7,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | spl11_23),
% 2.10/0.67    inference(resolution,[],[f1585,f93])).
% 2.10/0.67  fof(f93,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f28])).
% 2.10/0.67  fof(f28,plain,(
% 2.10/0.67    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.67    inference(flattening,[],[f27])).
% 2.10/0.67  fof(f27,plain,(
% 2.10/0.67    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f13])).
% 2.10/0.67  fof(f13,axiom,(
% 2.10/0.67    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 2.10/0.67  fof(f1585,plain,(
% 2.10/0.67    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | spl11_23),
% 2.10/0.67    inference(avatar_component_clause,[],[f1583])).
% 2.10/0.67  fof(f1583,plain,(
% 2.10/0.67    spl11_23 <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 2.10/0.67  fof(f1664,plain,(
% 2.10/0.67    spl11_22),
% 2.10/0.67    inference(avatar_contradiction_clause,[],[f1663])).
% 2.10/0.67  fof(f1663,plain,(
% 2.10/0.67    $false | spl11_22),
% 2.10/0.67    inference(subsumption_resolution,[],[f1662,f72])).
% 2.10/0.67  fof(f1662,plain,(
% 2.10/0.67    ~m1_subset_1(sK5,u1_struct_0(sK4)) | spl11_22),
% 2.10/0.67    inference(resolution,[],[f1595,f450])).
% 2.10/0.67  fof(f450,plain,(
% 2.10/0.67    m1_connsp_2(sK6,sK4,sK5)),
% 2.10/0.67    inference(subsumption_resolution,[],[f449,f69])).
% 2.10/0.67  fof(f449,plain,(
% 2.10/0.67    m1_connsp_2(sK6,sK4,sK5) | v2_struct_0(sK4)),
% 2.10/0.67    inference(subsumption_resolution,[],[f448,f70])).
% 2.10/0.67  fof(f448,plain,(
% 2.10/0.67    m1_connsp_2(sK6,sK4,sK5) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 2.10/0.67    inference(subsumption_resolution,[],[f447,f71])).
% 2.10/0.67  fof(f447,plain,(
% 2.10/0.67    m1_connsp_2(sK6,sK4,sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 2.10/0.67    inference(subsumption_resolution,[],[f443,f72])).
% 2.10/0.67  fof(f443,plain,(
% 2.10/0.67    m1_connsp_2(sK6,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 2.10/0.67    inference(resolution,[],[f82,f73])).
% 2.10/0.67  fof(f73,plain,(
% 2.10/0.67    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.67    inference(cnf_transformation,[],[f46])).
% 2.10/0.67  fof(f1595,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_connsp_2(sK6,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4))) ) | spl11_22),
% 2.10/0.67    inference(subsumption_resolution,[],[f1594,f69])).
% 2.10/0.67  fof(f1594,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_connsp_2(sK6,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | v2_struct_0(sK4)) ) | spl11_22),
% 2.10/0.67    inference(subsumption_resolution,[],[f1593,f70])).
% 2.10/0.67  fof(f1593,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_connsp_2(sK6,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | spl11_22),
% 2.10/0.67    inference(subsumption_resolution,[],[f1589,f71])).
% 2.10/0.67  fof(f1589,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_connsp_2(sK6,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | spl11_22),
% 2.10/0.67    inference(resolution,[],[f1581,f93])).
% 2.10/0.67  fof(f1581,plain,(
% 2.10/0.67    ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | spl11_22),
% 2.10/0.67    inference(avatar_component_clause,[],[f1579])).
% 2.10/0.67  fof(f1579,plain,(
% 2.10/0.67    spl11_22 <=> m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 2.10/0.67  fof(f1586,plain,(
% 2.10/0.67    ~spl11_22 | ~spl11_23 | ~spl11_8 | ~spl11_10 | spl11_21),
% 2.10/0.67    inference(avatar_split_clause,[],[f1577,f1504,f277,f268,f1583,f1579])).
% 2.10/0.67  fof(f268,plain,(
% 2.10/0.67    spl11_8 <=> sP0(sK4,sK6,sK5)),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 2.10/0.67  fof(f277,plain,(
% 2.10/0.67    spl11_10 <=> sP0(sK4,sK7,sK5)),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 2.10/0.67  fof(f1504,plain,(
% 2.10/0.67    spl11_21 <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK6,sK7)),sK4)),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 2.10/0.67  fof(f1577,plain,(
% 2.10/0.67    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | (~spl11_8 | ~spl11_10 | spl11_21)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1576,f70])).
% 2.10/0.67  fof(f1576,plain,(
% 2.10/0.67    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_pre_topc(sK4) | (~spl11_8 | ~spl11_10 | spl11_21)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1575,f71])).
% 2.10/0.67  fof(f1575,plain,(
% 2.10/0.67    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | (~spl11_8 | ~spl11_10 | spl11_21)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1574,f1436])).
% 2.10/0.67  fof(f1436,plain,(
% 2.10/0.67    v3_pre_topc(sK6,sK4) | ~spl11_8),
% 2.10/0.67    inference(resolution,[],[f270,f79])).
% 2.10/0.67  fof(f79,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v3_pre_topc(X1,X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f51])).
% 2.10/0.67  fof(f51,plain,(
% 2.10/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) & ((v3_pre_topc(X1,X0) & r2_hidden(X2,X1)) | ~sP0(X0,X1,X2)))),
% 2.10/0.67    inference(rectify,[],[f50])).
% 2.10/0.67  fof(f50,plain,(
% 2.10/0.67    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 2.10/0.67    inference(flattening,[],[f49])).
% 2.10/0.67  fof(f49,plain,(
% 2.10/0.67    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 2.10/0.67    inference(nnf_transformation,[],[f36])).
% 2.10/0.67  fof(f36,plain,(
% 2.10/0.67    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2)))),
% 2.10/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.10/0.67  fof(f270,plain,(
% 2.10/0.67    sP0(sK4,sK6,sK5) | ~spl11_8),
% 2.10/0.67    inference(avatar_component_clause,[],[f268])).
% 2.10/0.67  fof(f1574,plain,(
% 2.10/0.67    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | ~v3_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | (~spl11_10 | spl11_21)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1567,f1468])).
% 2.10/0.67  fof(f1468,plain,(
% 2.10/0.67    v3_pre_topc(sK7,sK4) | ~spl11_10),
% 2.10/0.67    inference(resolution,[],[f279,f79])).
% 2.10/0.67  fof(f279,plain,(
% 2.10/0.67    sP0(sK4,sK7,sK5) | ~spl11_10),
% 2.10/0.67    inference(avatar_component_clause,[],[f277])).
% 2.10/0.67  fof(f1567,plain,(
% 2.10/0.67    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | ~v3_pre_topc(sK7,sK4) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | ~v3_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | spl11_21),
% 2.10/0.67    inference(resolution,[],[f1506,f113])).
% 2.10/0.67  fof(f113,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.10/0.67    inference(definition_unfolding,[],[f99,f86])).
% 2.10/0.67  fof(f86,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f9])).
% 2.10/0.67  fof(f9,axiom,(
% 2.10/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.10/0.67  fof(f99,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f33])).
% 2.10/0.67  fof(f33,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.10/0.67    inference(flattening,[],[f32])).
% 2.10/0.67  fof(f32,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f12])).
% 2.10/0.67  fof(f12,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).
% 2.10/0.67  fof(f1506,plain,(
% 2.10/0.67    ~v3_pre_topc(k1_setfam_1(k2_tarski(sK6,sK7)),sK4) | spl11_21),
% 2.10/0.67    inference(avatar_component_clause,[],[f1504])).
% 2.10/0.67  fof(f1520,plain,(
% 2.10/0.67    ~spl11_8 | ~spl11_10 | spl11_20),
% 2.10/0.67    inference(avatar_contradiction_clause,[],[f1519])).
% 2.10/0.67  fof(f1519,plain,(
% 2.10/0.67    $false | (~spl11_8 | ~spl11_10 | spl11_20)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1518,f1437])).
% 2.10/0.67  fof(f1437,plain,(
% 2.10/0.67    r2_hidden(sK5,sK6) | ~spl11_8),
% 2.10/0.67    inference(resolution,[],[f270,f78])).
% 2.10/0.67  fof(f78,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X2,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f51])).
% 2.10/0.67  fof(f1518,plain,(
% 2.10/0.67    ~r2_hidden(sK5,sK6) | (~spl11_10 | spl11_20)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1517,f1469])).
% 2.10/0.67  fof(f1469,plain,(
% 2.10/0.67    r2_hidden(sK5,sK7) | ~spl11_10),
% 2.10/0.67    inference(resolution,[],[f279,f78])).
% 2.10/0.67  fof(f1517,plain,(
% 2.10/0.67    ~r2_hidden(sK5,sK7) | ~r2_hidden(sK5,sK6) | spl11_20),
% 2.10/0.67    inference(resolution,[],[f1508,f107])).
% 2.10/0.67  fof(f107,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f67])).
% 2.10/0.67  fof(f67,plain,(
% 2.10/0.67    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 2.10/0.67    inference(rectify,[],[f66])).
% 2.10/0.67  fof(f66,plain,(
% 2.10/0.67    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 2.10/0.67    inference(flattening,[],[f65])).
% 2.10/0.67  fof(f65,plain,(
% 2.10/0.67    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 2.10/0.67    inference(nnf_transformation,[],[f39])).
% 2.10/0.67  fof(f39,plain,(
% 2.10/0.67    ! [X1,X3,X0] : (sP2(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 2.10/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.10/0.67  fof(f1508,plain,(
% 2.10/0.67    ~sP2(sK7,sK5,sK6) | spl11_20),
% 2.10/0.67    inference(resolution,[],[f1502,f204])).
% 2.10/0.67  fof(f204,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X0))) | ~sP2(X0,X1,X2)) )),
% 2.10/0.67    inference(resolution,[],[f102,f116])).
% 2.10/0.67  fof(f116,plain,(
% 2.10/0.67    ( ! [X0,X1] : (sP3(X0,X1,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.10/0.67    inference(equality_resolution,[],[f115])).
% 2.10/0.67  fof(f115,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 2.10/0.67    inference(definition_unfolding,[],[f108,f86])).
% 2.10/0.67  fof(f108,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.10/0.67    inference(cnf_transformation,[],[f68])).
% 2.10/0.67  fof(f68,plain,(
% 2.10/0.67    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 2.10/0.67    inference(nnf_transformation,[],[f41])).
% 2.10/0.67  fof(f41,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 2.10/0.67    inference(definition_folding,[],[f3,f40,f39])).
% 2.10/0.67  fof(f40,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X3,X0)))),
% 2.10/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.10/0.67  fof(f3,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.10/0.67  fof(f102,plain,(
% 2.10/0.67    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~sP2(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f64])).
% 2.10/0.67  % (12718)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.10/0.68  % (12716)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.10/0.68  % (12717)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.10/0.68  fof(f64,plain,(
% 2.10/0.68    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP2(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 2.10/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f62,f63])).
% 2.10/0.68  fof(f63,plain,(
% 2.10/0.68    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP2(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP2(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 2.10/0.68    introduced(choice_axiom,[])).
% 2.10/0.68  fof(f62,plain,(
% 2.10/0.68    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 2.10/0.68    inference(rectify,[],[f61])).
% 2.10/0.68  fof(f61,plain,(
% 2.10/0.68    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X3,X0)) & (sP2(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 2.10/0.68    inference(nnf_transformation,[],[f40])).
% 2.10/0.68  fof(f1502,plain,(
% 2.10/0.68    ~r2_hidden(sK5,k1_setfam_1(k2_tarski(sK6,sK7))) | spl11_20),
% 2.10/0.68    inference(avatar_component_clause,[],[f1500])).
% 2.10/0.68  fof(f1500,plain,(
% 2.10/0.68    spl11_20 <=> r2_hidden(sK5,k1_setfam_1(k2_tarski(sK6,sK7)))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 2.10/0.68  fof(f1507,plain,(
% 2.10/0.68    ~spl11_20 | ~spl11_21 | spl11_12),
% 2.10/0.68    inference(avatar_split_clause,[],[f1492,f298,f1504,f1500])).
% 2.10/0.68  fof(f298,plain,(
% 2.10/0.68    spl11_12 <=> sP0(sK4,k1_setfam_1(k2_tarski(sK6,sK7)),sK5)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 2.10/0.68  fof(f1492,plain,(
% 2.10/0.68    ~v3_pre_topc(k1_setfam_1(k2_tarski(sK6,sK7)),sK4) | ~r2_hidden(sK5,k1_setfam_1(k2_tarski(sK6,sK7))) | spl11_12),
% 2.10/0.68    inference(resolution,[],[f300,f80])).
% 2.10/0.68  fof(f80,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f51])).
% 2.10/0.68  fof(f300,plain,(
% 2.10/0.68    ~sP0(sK4,k1_setfam_1(k2_tarski(sK6,sK7)),sK5) | spl11_12),
% 2.10/0.68    inference(avatar_component_clause,[],[f298])).
% 2.10/0.68  fof(f1485,plain,(
% 2.10/0.68    spl11_11),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f1484])).
% 2.10/0.68  fof(f1484,plain,(
% 2.10/0.68    $false | spl11_11),
% 2.10/0.68    inference(subsumption_resolution,[],[f1483,f72])).
% 2.10/0.68  fof(f1483,plain,(
% 2.10/0.68    ~m1_subset_1(sK5,u1_struct_0(sK4)) | spl11_11),
% 2.10/0.68    inference(resolution,[],[f1463,f454])).
% 2.10/0.68  fof(f1463,plain,(
% 2.10/0.68    ( ! [X0] : (~m1_connsp_2(sK7,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4))) ) | spl11_11),
% 2.10/0.68    inference(subsumption_resolution,[],[f1462,f69])).
% 2.10/0.68  fof(f1462,plain,(
% 2.10/0.68    ( ! [X0] : (~m1_connsp_2(sK7,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | v2_struct_0(sK4)) ) | spl11_11),
% 2.10/0.68    inference(subsumption_resolution,[],[f1461,f70])).
% 2.10/0.68  fof(f1461,plain,(
% 2.10/0.68    ( ! [X0] : (~m1_connsp_2(sK7,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | spl11_11),
% 2.10/0.68    inference(subsumption_resolution,[],[f1457,f71])).
% 2.10/0.68  fof(f1457,plain,(
% 2.10/0.68    ( ! [X0] : (~m1_connsp_2(sK7,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | spl11_11),
% 2.10/0.68    inference(resolution,[],[f1455,f93])).
% 2.10/0.68  fof(f1455,plain,(
% 2.10/0.68    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | spl11_11),
% 2.10/0.68    inference(subsumption_resolution,[],[f1454,f69])).
% 2.10/0.68  fof(f1454,plain,(
% 2.10/0.68    v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | spl11_11),
% 2.10/0.68    inference(subsumption_resolution,[],[f1453,f70])).
% 2.10/0.68  fof(f1453,plain,(
% 2.10/0.68    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | spl11_11),
% 2.10/0.68    inference(subsumption_resolution,[],[f1452,f71])).
% 2.10/0.68  fof(f1452,plain,(
% 2.10/0.68    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | spl11_11),
% 2.10/0.68    inference(subsumption_resolution,[],[f1451,f72])).
% 2.10/0.68  fof(f1451,plain,(
% 2.10/0.68    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | spl11_11),
% 2.10/0.68    inference(duplicate_literal_removal,[],[f1438])).
% 2.10/0.68  fof(f1438,plain,(
% 2.10/0.68    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | spl11_11),
% 2.10/0.68    inference(resolution,[],[f355,f303])).
% 2.10/0.68  fof(f303,plain,(
% 2.10/0.68    ( ! [X0] : (~sP1(sK5,k9_subset_1(X0,sK6,sK7),sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(X0))) ) | spl11_11),
% 2.10/0.68    inference(superposition,[],[f296,f112])).
% 2.10/0.68  fof(f112,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(definition_unfolding,[],[f98,f86])).
% 2.10/0.68  fof(f98,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f31])).
% 2.10/0.68  fof(f31,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f8])).
% 2.10/0.68  fof(f8,axiom,(
% 2.10/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.10/0.68  fof(f296,plain,(
% 2.10/0.68    ~sP1(sK5,k1_setfam_1(k2_tarski(sK6,sK7)),sK4) | spl11_11),
% 2.10/0.68    inference(avatar_component_clause,[],[f294])).
% 2.10/0.68  fof(f294,plain,(
% 2.10/0.68    spl11_11 <=> sP1(sK5,k1_setfam_1(k2_tarski(sK6,sK7)),sK4)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 2.10/0.68  fof(f355,plain,(
% 2.10/0.68    ( ! [X2,X0,X3,X1] : (sP1(X0,k9_subset_1(u1_struct_0(X1),X2,X3),X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 2.10/0.68    inference(resolution,[],[f81,f97])).
% 2.10/0.68  fof(f97,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f30])).
% 2.10/0.68  fof(f30,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f7])).
% 2.10/0.68  fof(f7,axiom,(
% 2.10/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 2.10/0.68  fof(f81,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X1,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f38])).
% 2.10/0.68  fof(f38,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.68    inference(definition_folding,[],[f21,f37,f36])).
% 2.10/0.68  fof(f37,plain,(
% 2.10/0.68    ! [X1,X2,X0] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 2.10/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.10/0.68  fof(f21,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.68    inference(flattening,[],[f20])).
% 2.10/0.68  fof(f20,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f14])).
% 2.10/0.68  fof(f14,axiom,(
% 2.10/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 2.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 2.10/0.68  fof(f1467,plain,(
% 2.10/0.68    spl11_9),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f1466])).
% 2.10/0.68  fof(f1466,plain,(
% 2.10/0.68    $false | spl11_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f1465,f72])).
% 2.10/0.68  fof(f1465,plain,(
% 2.10/0.68    ~m1_subset_1(sK5,u1_struct_0(sK4)) | spl11_9),
% 2.10/0.68    inference(resolution,[],[f1431,f454])).
% 2.10/0.68  fof(f1431,plain,(
% 2.10/0.68    ( ! [X4] : (~m1_connsp_2(sK7,sK4,X4) | ~m1_subset_1(X4,u1_struct_0(sK4))) ) | spl11_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f1430,f72])).
% 2.10/0.68  fof(f1430,plain,(
% 2.10/0.68    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK4)) | ~m1_connsp_2(sK7,sK4,X4) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | spl11_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f1429,f69])).
% 2.10/0.68  fof(f1429,plain,(
% 2.10/0.68    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK4)) | v2_struct_0(sK4) | ~m1_connsp_2(sK7,sK4,X4) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | spl11_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f1428,f70])).
% 2.10/0.68  fof(f1428,plain,(
% 2.10/0.68    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_connsp_2(sK7,sK4,X4) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | spl11_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f1414,f71])).
% 2.10/0.68  fof(f1414,plain,(
% 2.10/0.68    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_connsp_2(sK7,sK4,X4) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | spl11_9),
% 2.10/0.68    inference(resolution,[],[f408,f275])).
% 2.10/0.68  fof(f275,plain,(
% 2.10/0.68    ~sP1(sK5,sK7,sK4) | spl11_9),
% 2.10/0.68    inference(avatar_component_clause,[],[f273])).
% 2.10/0.68  fof(f273,plain,(
% 2.10/0.68    spl11_9 <=> sP1(sK5,sK7,sK4)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 2.10/0.68  fof(f408,plain,(
% 2.10/0.68    ( ! [X2,X0,X3,X1] : (sP1(X3,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_connsp_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.10/0.68    inference(duplicate_literal_removal,[],[f403])).
% 2.10/0.68  fof(f403,plain,(
% 2.10/0.68    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X3,X0,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.10/0.68    inference(resolution,[],[f93,f81])).
% 2.10/0.68  fof(f1435,plain,(
% 2.10/0.68    spl11_7),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f1434])).
% 2.10/0.68  fof(f1434,plain,(
% 2.10/0.68    $false | spl11_7),
% 2.10/0.68    inference(subsumption_resolution,[],[f1433,f72])).
% 2.10/0.68  fof(f1433,plain,(
% 2.10/0.68    ~m1_subset_1(sK5,u1_struct_0(sK4)) | spl11_7),
% 2.10/0.68    inference(resolution,[],[f1427,f450])).
% 2.10/0.68  fof(f1427,plain,(
% 2.10/0.68    ( ! [X3] : (~m1_connsp_2(sK6,sK4,X3) | ~m1_subset_1(X3,u1_struct_0(sK4))) ) | spl11_7),
% 2.10/0.68    inference(subsumption_resolution,[],[f1426,f72])).
% 2.10/0.68  fof(f1426,plain,(
% 2.10/0.68    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_connsp_2(sK6,sK4,X3) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | spl11_7),
% 2.10/0.68    inference(subsumption_resolution,[],[f1425,f69])).
% 2.10/0.68  fof(f1425,plain,(
% 2.10/0.68    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK4)) | v2_struct_0(sK4) | ~m1_connsp_2(sK6,sK4,X3) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | spl11_7),
% 2.10/0.68    inference(subsumption_resolution,[],[f1424,f70])).
% 2.10/0.68  fof(f1424,plain,(
% 2.10/0.68    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_connsp_2(sK6,sK4,X3) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | spl11_7),
% 2.10/0.68    inference(subsumption_resolution,[],[f1413,f71])).
% 2.10/0.68  fof(f1413,plain,(
% 2.10/0.68    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_connsp_2(sK6,sK4,X3) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | spl11_7),
% 2.10/0.68    inference(resolution,[],[f408,f266])).
% 2.10/0.68  fof(f266,plain,(
% 2.10/0.68    ~sP1(sK5,sK6,sK4) | spl11_7),
% 2.10/0.68    inference(avatar_component_clause,[],[f264])).
% 2.10/0.68  fof(f264,plain,(
% 2.10/0.68    spl11_7 <=> sP1(sK5,sK6,sK4)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 2.10/0.68  fof(f656,plain,(
% 2.10/0.68    ~spl11_5),
% 2.10/0.68    inference(avatar_split_clause,[],[f637,f142])).
% 2.10/0.68  fof(f142,plain,(
% 2.10/0.68    spl11_5 <=> v1_xboole_0(sK7)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 2.10/0.68  fof(f637,plain,(
% 2.10/0.68    ~v1_xboole_0(sK7)),
% 2.10/0.68    inference(resolution,[],[f629,f187])).
% 2.10/0.68  fof(f187,plain,(
% 2.10/0.68    ~sP3(sK6,sK7,sK7)),
% 2.10/0.68    inference(resolution,[],[f180,f74])).
% 2.10/0.68  fof(f180,plain,(
% 2.10/0.68    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK4,sK5))) | ~sP3(sK6,sK7,X1)) )),
% 2.10/0.68    inference(superposition,[],[f110,f114])).
% 2.10/0.68  fof(f114,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~sP3(X0,X1,X2)) )),
% 2.10/0.68    inference(definition_unfolding,[],[f109,f86])).
% 2.10/0.68  fof(f109,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f68])).
% 2.10/0.68  fof(f110,plain,(
% 2.10/0.68    ~m1_subset_1(k1_setfam_1(k2_tarski(sK6,sK7)),u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.68    inference(definition_unfolding,[],[f75,f86])).
% 2.10/0.68  fof(f75,plain,(
% 2.10/0.68    ~m1_subset_1(k3_xboole_0(sK6,sK7),u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.68    inference(cnf_transformation,[],[f46])).
% 2.10/0.68  fof(f629,plain,(
% 2.10/0.68    ( ! [X0,X1] : (sP3(X0,X1,X1) | ~v1_xboole_0(X1)) )),
% 2.10/0.68    inference(resolution,[],[f628,f83])).
% 2.10/0.68  fof(f83,plain,(
% 2.10/0.68    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f55])).
% 2.10/0.68  fof(f55,plain,(
% 2.10/0.68    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.10/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f53,f54])).
% 2.10/0.68  fof(f54,plain,(
% 2.10/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 2.10/0.68    introduced(choice_axiom,[])).
% 2.10/0.68  fof(f53,plain,(
% 2.10/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.10/0.68    inference(rectify,[],[f52])).
% 2.10/0.68  fof(f52,plain,(
% 2.10/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.10/0.68    inference(nnf_transformation,[],[f1])).
% 2.10/0.68  fof(f1,axiom,(
% 2.10/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.10/0.68  fof(f628,plain,(
% 2.10/0.68    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1,X1),X1) | sP3(X0,X1,X1)) )),
% 2.10/0.68    inference(factoring,[],[f310])).
% 2.10/0.68  fof(f310,plain,(
% 2.10/0.68    ( ! [X4,X5,X3] : (r2_hidden(sK10(X3,X4,X5),X5) | sP3(X3,X4,X5) | r2_hidden(sK10(X3,X4,X5),X4)) )),
% 2.10/0.68    inference(resolution,[],[f103,f106])).
% 2.10/0.68  fof(f106,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f67])).
% 2.10/0.68  fof(f103,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (sP2(X1,sK10(X0,X1,X2),X0) | sP3(X0,X1,X2) | r2_hidden(sK10(X0,X1,X2),X2)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f64])).
% 2.10/0.68  fof(f301,plain,(
% 2.10/0.68    ~spl11_11 | ~spl11_12),
% 2.10/0.68    inference(avatar_split_clause,[],[f290,f298,f294])).
% 2.10/0.68  fof(f290,plain,(
% 2.10/0.68    ~sP0(sK4,k1_setfam_1(k2_tarski(sK6,sK7)),sK5) | ~sP1(sK5,k1_setfam_1(k2_tarski(sK6,sK7)),sK4)),
% 2.10/0.68    inference(resolution,[],[f77,f118])).
% 2.10/0.68  fof(f118,plain,(
% 2.10/0.68    ~r2_hidden(k1_setfam_1(k2_tarski(sK6,sK7)),u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.68    inference(resolution,[],[f92,f110])).
% 2.10/0.68  fof(f92,plain,(
% 2.10/0.68    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f26])).
% 2.10/0.68  fof(f26,plain,(
% 2.10/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.10/0.68    inference(ennf_transformation,[],[f10])).
% 2.10/0.68  fof(f10,axiom,(
% 2.10/0.68    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 2.10/0.68  fof(f77,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f48])).
% 2.10/0.68  fof(f48,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (((r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))))) | ~sP1(X0,X1,X2))),
% 2.10/0.68    inference(rectify,[],[f47])).
% 2.10/0.68  fof(f47,plain,(
% 2.10/0.68    ! [X1,X2,X0] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~sP1(X1,X2,X0))),
% 2.10/0.68    inference(nnf_transformation,[],[f37])).
% 2.10/0.68  fof(f280,plain,(
% 2.10/0.68    ~spl11_9 | spl11_10 | spl11_3),
% 2.10/0.68    inference(avatar_split_clause,[],[f260,f133,f277,f273])).
% 2.10/0.68  fof(f133,plain,(
% 2.10/0.68    spl11_3 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 2.10/0.68  fof(f260,plain,(
% 2.10/0.68    sP0(sK4,sK7,sK5) | ~sP1(sK5,sK7,sK4) | spl11_3),
% 2.10/0.68    inference(resolution,[],[f76,f161])).
% 2.10/0.68  fof(f161,plain,(
% 2.10/0.68    r2_hidden(sK7,u1_struct_0(k9_yellow_6(sK4,sK5))) | spl11_3),
% 2.10/0.68    inference(subsumption_resolution,[],[f156,f135])).
% 2.10/0.68  fof(f135,plain,(
% 2.10/0.68    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5))) | spl11_3),
% 2.10/0.68    inference(avatar_component_clause,[],[f133])).
% 2.10/0.68  fof(f156,plain,(
% 2.10/0.68    r2_hidden(sK7,u1_struct_0(k9_yellow_6(sK4,sK5))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.68    inference(resolution,[],[f87,f74])).
% 2.10/0.68  fof(f87,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f56])).
% 2.10/0.68  fof(f56,plain,(
% 2.10/0.68    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.10/0.68    inference(nnf_transformation,[],[f24])).
% 2.10/0.68  fof(f24,plain,(
% 2.10/0.68    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f6])).
% 2.10/0.68  fof(f6,axiom,(
% 2.10/0.68    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.10/0.68  fof(f76,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f48])).
% 2.10/0.68  fof(f271,plain,(
% 2.10/0.68    ~spl11_7 | spl11_8 | spl11_3),
% 2.10/0.68    inference(avatar_split_clause,[],[f259,f133,f268,f264])).
% 2.10/0.68  fof(f259,plain,(
% 2.10/0.68    sP0(sK4,sK6,sK5) | ~sP1(sK5,sK6,sK4) | spl11_3),
% 2.10/0.68    inference(resolution,[],[f76,f160])).
% 2.10/0.68  fof(f160,plain,(
% 2.10/0.68    r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK4,sK5))) | spl11_3),
% 2.10/0.68    inference(subsumption_resolution,[],[f155,f135])).
% 2.10/0.68  fof(f155,plain,(
% 2.10/0.68    r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK4,sK5))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.68    inference(resolution,[],[f87,f73])).
% 2.10/0.68  fof(f145,plain,(
% 2.10/0.68    ~spl11_3 | spl11_5),
% 2.10/0.68    inference(avatar_split_clause,[],[f121,f142,f133])).
% 2.10/0.68  fof(f121,plain,(
% 2.10/0.68    v1_xboole_0(sK7) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK4,sK5)))),
% 2.10/0.68    inference(resolution,[],[f89,f74])).
% 2.10/0.68  fof(f89,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f56])).
% 2.10/0.68  % SZS output end Proof for theBenchmark
% 2.10/0.68  % (12712)------------------------------
% 2.10/0.68  % (12712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.68  % (12712)Termination reason: Refutation
% 2.10/0.68  
% 2.10/0.68  % (12712)Memory used [KB]: 6908
% 2.10/0.68  % (12712)Time elapsed: 0.268 s
% 2.10/0.68  % (12712)------------------------------
% 2.10/0.68  % (12712)------------------------------
% 2.10/0.69  % (12683)Success in time 0.325 s
%------------------------------------------------------------------------------
